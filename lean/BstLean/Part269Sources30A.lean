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
import BstLean.Part269Direction30
import BstLean.Part269Shared30
import BstLean.Part269Finite
import BstLean.Part269Rows30
import BstLean.Part269Source
/-! Actual 13100 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13100 ≤ (1.035253505778 : ℝ) := by
  have hr : (114.455231422595 : ℝ) ≤ √(13100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.455231422595 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13100 13100 (11 / 1000) ≤
    (0.008351622770 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13100) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.455231422595 : ℝ) ≤ √(13100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13100)
  have hdiv : K / √(13100 : ℝ) ≤ K / 114.455231422595 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.455231422595 ≤ (0.008351622770 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13100.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13100 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13100 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13100 := gPlus_lower 13100
end BstLean.Part269.N13100

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13100
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035253505777 : ℝ) ≤ wn 13100 := by
  have hn : √(13100 : ℝ) ≤ 114.455231422596 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13100 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.455231422596 ≤ 2 / √(13100 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244058841 : ℝ) ≤ rhoBar 13100 BstLean.Part154.csC ∧
    rhoBar 13100 BstLean.Part154.csC ≤ 0.000244059219 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035253505777 : ℝ) / (1.295212 * 13100) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035253505778 : ℝ) / (1.29521 * 13100) := by gcongr
      _ ≤ (0.000244059219 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13100 BstLean.Part154.csC) ≤ 0.000976296441 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13100 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) ≤ 0.000186413809 ∧
    cc1 (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) ≤ 0.000118616400 ∧
    cc2 (rhoBar 13100 BstLean.Part154.csC) ≤ 0.000068857796 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13100 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13100 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13100 BstLean.Part154.csC * nuR (rhoBar 13100 BstLean.Part154.csC)) ≤ 0.000488133330 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244059219 : ℝ) * 0.000976296441 := by gcongr
      _ ≤ (0.000488133330 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13100 BstLean.Part154.csC) * nuR (rhoBar 13100 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976296441 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13100 BstLean.Part154.csC) * rhoBar 13100 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244059219 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244059219 / 2 + 0.399 * 0.000976296441 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186413809 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488133330 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118616400 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244059219 / 1.414213562 := by gcongr
      _ ≤ (0.000068857796 : ℝ) := by norm_num

end BstLean.Part269.N13100

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13100
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) ≤ 1.50069E-7 := by
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13100 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13100 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13100 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186413809 : ℝ) ^ 2 + 0.000118616400 ^ 2 + 3 * 0.000068857796 ^ 2 +
        2 * 0.797885 * 0.000186413809 * 0.000118616400 + 2 * 0.000186413809 * 0.000068857796 +
        4 * 0.797885 * 0.000118616400 * 0.000068857796 := by gcongr
    _ ≤ (1.50069E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13100 BstLean.Part154.csC Θ ≤ 0.002546262332 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13100 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13100 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13100 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035253505778 * 1.50069E-7 / (0.000244058841 : ℝ) := by gcongr
    _ ≤ 0.002546262332 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13100 BstLean.Part154.csC Θ ≤ 0.002823703790 + 0.000643401593 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13100 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13100 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035253505778 : ℝ) * ((2 * Θ * 0.000244059219 +
        (6863 / 10000) * 0.000244059219 * 13100 * 0.000976296441) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002823703790 + 0.000643401593 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13100 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13100 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13100 0.011 Θ ∧ gammaRatio 13100 0.011 Θ ≤ 0.000083901249 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13100 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035253505778 : ℝ) * 0.525 / ((1 - 0.011) * 13100) := by gcongr
      _ ≤ (0.000083901249 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13100 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13100 0.011 Θ) :=
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
    badAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13100 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13100 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13100 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13100 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13100 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13100 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13100 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13100 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13100 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13100 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035253505778 : ℝ) * 13100 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172609372 + 0.003189663925 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13100

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13100
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13100 BstLean.Part154.csC) (piBar (rhoBar 13100 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13100 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13100 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13100 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13100 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13100 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13100 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13100 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13100 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13100 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13100 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051668192304 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13100) ≤ 0.010434102192 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13100 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035253505778)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010434102192 + 2 * 0.737676 / 13100) := by gcongr
    _ ≤ (0.051668192304 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13100 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13100

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13100
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521105137 : ℝ) ≤ plow 13100 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13100) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353782933)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336787725) : eMP 13100 0.011 xi bn ≤ 0.001151376755 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13100 : ℝ) * (1 - 0.011))) ≤ 0.000569340911 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336787725 / (13100 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569340911 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569340911 : ℝ) + 3.141593 * 0.052353782933 / (13100 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151376755 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353782933)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336787725) : PiBarMP 13100 12 0.011 xi bn ≤ 0.158745649182 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13100 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036562107776 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.823986927185 : ℝ) ≤ √((13100 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.455231422595 : ℝ) ≤ √(13100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13100) ≤ 0.121728016183 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036562107776 + 0.052353782933 * 1.772454 / (2 * (113.823986927185 : ℝ))) * (1 + 0.001151376755) +
        8 / (13100 * 114.455231422595) + 0.121728016183 := by gcongr
    _ ≤ (0.158745649182 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353782933)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336787725) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280477682783) :
    parallelOracle 13100 0.011 xi bn cd ≤ 0.159705770472 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13100 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13100 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521105137 : ℝ) ≤ plow 13100 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.455231422595 : ℝ) ≤ √(13100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280477682783 : ℝ) / (2 * 0.560521105137 * 114.455231422595)) * 0.158745649182 +
        0.280477682783 ^ 2 / (2 * 0.560521105137 * 114.455231422595) := by gcongr
    _ ≤ (0.159705770472 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353782933) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336787725)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280477682783) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13100 13100 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521105137 : ℝ) ≤ plow 13100 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.455231422595 : ℝ) ≤ √(13100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13100 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13100 Θ 1.22 ≤ 0.011586193864 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.455231422595 := by gcongr <;> linarith
      _ ≤ (0.011586193864 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13100 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13100 13100 0.011 ≤ 0.008351622770 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13100 13100 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13100 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13100 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13100 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13100 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159705770472 + 0.011586193864 + (0.008351622770 : ℝ) *
        (1 + 2 * (0.280477682783 + 0.011586193864) / (0.560521105137 * 114.455231422595))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13100]

end BstLean.Part269.N13100

/-! The original eight local profiles supply actual 13100 moment certificates. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13100 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052353782933 ∧
    0 ≤ bN 13100 BstLean.Part154.csC (groupTheta g) ∧ bN 13100 BstLean.Part154.csC (groupTheta g) ≤ 0.001336787725 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13100 13100 0.011
      (momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13100 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13100 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13100 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228809490479 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13100 0.011
      (momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13100 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13100
/-! The actual computed-centre upper energy formula at 13100. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13100

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13100)
open BstLean.Part268 (cell13100)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084402170660
  | 2 => 0.085327524542
  | 3 => 0.086248594455
  | 4 => 0.087166228491
  | 5 => 0.088081468809
  | 6 => 0.088995582450
  | 7 => 0.089910095452
  | 8 => 0.090826830347
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13100 13100 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13100 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13100

/-! Actual upper energy certificates on all 43 source endpoints at 13100. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13100)
open BstLean.Part268 (cell13100)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13100 (gMinus 13100) (1 - (cell13100 i).lower) ≤ 1 ∧
    energyUpper 13100 (gMinus 13100) (BstLean.Part211.gPlus 13100)
      (finiteEnergy 13100 13100 0.011) (1 - (cell13100 i).lower) ≤
      (cell13100 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨10,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨11,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨12,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨13,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨14,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨15,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨16,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨17,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨18,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨19,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨20,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨21,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨22,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨23,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨24,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨25,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨26,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨27,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨28,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨29,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨30,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨31,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨32,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨33,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨34,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨35,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨36,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨37,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨38,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨39,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨40,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨41,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨42,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨43,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨44,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨45,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨46,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨47,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨48,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨49,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨50,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨51,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13100) (by norm_num)
        (q := 1 - (cell13100 ⟨52,by decide⟩).lower)
        (by norm_num [cell13100]) (by norm_num [cell13100])
      exact ⟨E.1,E.2.trans (by norm_num [cell13100])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13100

/-! Source-cell containment and simple scalar guards at 13100. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13100)
open BstLean.Part268 (cell13100)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13100 ⟨10,by decide⟩).lower ∧ (cell13100 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13100 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13100 ⟨11,by decide⟩).lower ∧ (cell13100 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13100 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13100 ⟨12,by decide⟩).lower ∧ (cell13100 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13100 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13100 ⟨13,by decide⟩).lower ∧ (cell13100 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13100 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13100 ⟨14,by decide⟩).lower ∧ (cell13100 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13100 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13100 ⟨15,by decide⟩).lower ∧ (cell13100 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13100 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13100 ⟨16,by decide⟩).lower ∧ (cell13100 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13100 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13100 ⟨17,by decide⟩).lower ∧ (cell13100 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13100 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13100 ⟨18,by decide⟩).lower ∧ (cell13100 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13100 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13100 ⟨19,by decide⟩).lower ∧ (cell13100 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13100 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13100 ⟨20,by decide⟩).lower ∧ (cell13100 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13100 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13100 ⟨21,by decide⟩).lower ∧ (cell13100 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13100 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13100 ⟨22,by decide⟩).lower ∧ (cell13100 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13100 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13100 ⟨23,by decide⟩).lower ∧ (cell13100 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13100 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13100 ⟨24,by decide⟩).lower ∧ (cell13100 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13100 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13100 ⟨25,by decide⟩).lower ∧ (cell13100 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13100 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13100 ⟨26,by decide⟩).lower ∧ (cell13100 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13100 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13100 ⟨27,by decide⟩).lower ∧ (cell13100 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13100 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13100 ⟨28,by decide⟩).lower ∧ (cell13100 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13100 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13100 ⟨29,by decide⟩).lower ∧ (cell13100 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13100 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13100 ⟨30,by decide⟩).lower ∧ (cell13100 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13100 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13100 ⟨31,by decide⟩).lower ∧ (cell13100 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13100 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13100 ⟨32,by decide⟩).lower ∧ (cell13100 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13100 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13100 ⟨33,by decide⟩).lower ∧ (cell13100 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13100 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13100 ⟨34,by decide⟩).lower ∧ (cell13100 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13100 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13100 ⟨35,by decide⟩).lower ∧ (cell13100 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13100 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13100 ⟨36,by decide⟩).lower ∧ (cell13100 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13100 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13100 ⟨37,by decide⟩).lower ∧ (cell13100 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13100 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13100 ⟨38,by decide⟩).lower ∧ (cell13100 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13100 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13100 ⟨39,by decide⟩).lower ∧ (cell13100 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13100 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13100 ⟨40,by decide⟩).lower ∧ (cell13100 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13100 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13100 ⟨41,by decide⟩).lower ∧ (cell13100 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13100 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13100 ⟨42,by decide⟩).lower ∧ (cell13100 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13100 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13100 ⟨43,by decide⟩).lower ∧ (cell13100 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13100 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13100 ⟨44,by decide⟩).lower ∧ (cell13100 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13100 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13100 ⟨45,by decide⟩).lower ∧ (cell13100 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13100 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13100 ⟨46,by decide⟩).lower ∧ (cell13100 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13100 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13100 ⟨47,by decide⟩).lower ∧ (cell13100 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13100 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13100 ⟨48,by decide⟩).lower ∧ (cell13100 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13100 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13100 ⟨49,by decide⟩).lower ∧ (cell13100 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13100 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13100 ⟨50,by decide⟩).lower ∧ (cell13100 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13100 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13100 ⟨51,by decide⟩).lower ∧ (cell13100 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13100 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13100 ⟨52,by decide⟩).lower ∧ (cell13100 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13100 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13100 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13100 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13100,cell13100,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13100 i).lower ∧
    (cell13100 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13100 i).upper ≤ (0.532 : ℝ) ∧
    (cell13100 i).centre ≤ (0.1 : ℝ) ∧ (cell13100 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13100 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13100 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13100

/-! The local source numeric instances at 13100 have no network premises. -/
namespace BstLean.Part269.N13100
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13100)
open BstLean.Part268 (cell13100)

noncomputable def sourceNumerics13100 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13100 (cell13100 i)
      scalarRow13100.M scalarRow13100.H scalarRow13100.xi := by
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
    energy_allowance := scalarRow13100.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13100]
    centre_nonneg := (scalarRow13100.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13100])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13100
/-! Actual 13101 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13101 ≤ (1.035252148649 : ℝ) := by
  have hr : (114.459599859513 : ℝ) ≤ √(13101 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.459599859513 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13101 13101 (11 / 1000) ≤
    (0.008351304022 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13101) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.459599859513 : ℝ) ≤ √(13101 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13101)
  have hdiv : K / √(13101 : ℝ) ≤ K / 114.459599859513 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.459599859513 ≤ (0.008351304022 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13101.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13101 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13101 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13101 := gPlus_lower 13101
end BstLean.Part269.N13101

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13101
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035252148648 : ℝ) ≤ wn 13101 := by
  have hn : √(13101 : ℝ) ≤ 114.459599859514 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13101 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.459599859514 ≤ 2 / √(13101 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244039892 : ℝ) ≤ rhoBar 13101 BstLean.Part154.csC ∧
    rhoBar 13101 BstLean.Part154.csC ≤ 0.000244040270 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035252148648 : ℝ) / (1.295212 * 13101) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035252148649 : ℝ) / (1.29521 * 13101) := by gcongr
      _ ≤ (0.000244040270 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13101 BstLean.Part154.csC) ≤ 0.000976220636 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13101 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) ≤ 0.000186399335 ∧
    cc1 (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) ≤ 0.000118607190 ∧
    cc2 (rhoBar 13101 BstLean.Part154.csC) ≤ 0.000068852450 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13101 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13101 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13101 BstLean.Part154.csC * nuR (rhoBar 13101 BstLean.Part154.csC)) ≤ 0.000488095429 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244040270 : ℝ) * 0.000976220636 := by gcongr
      _ ≤ (0.000488095429 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13101 BstLean.Part154.csC) * nuR (rhoBar 13101 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976220636 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13101 BstLean.Part154.csC) * rhoBar 13101 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244040270 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244040270 / 2 + 0.399 * 0.000976220636 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186399335 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488095429 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118607190 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244040270 / 1.414213562 := by gcongr
      _ ≤ (0.000068852450 : ℝ) := by norm_num

end BstLean.Part269.N13101

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13101
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) ≤ 1.50046E-7 := by
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13101 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13101 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13101 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186399335 : ℝ) ^ 2 + 0.000118607190 ^ 2 + 3 * 0.000068852450 ^ 2 +
        2 * 0.797885 * 0.000186399335 * 0.000118607190 + 2 * 0.000186399335 * 0.000068852450 +
        4 * 0.797885 * 0.000118607190 * 0.000068852450 := by gcongr
    _ ≤ (1.50046E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13101 BstLean.Part154.csC Θ ≤ 0.002546066426 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13101 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13101 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13101 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035252148649 * 1.50046E-7 / (0.000244039892 : ℝ) := by gcongr
    _ ≤ 0.002546066426 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13101 BstLean.Part154.csC Θ ≤ 0.002823477139 + 0.000643350796 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13101 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13101 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035252148649 : ℝ) * ((2 * Θ * 0.000244040270 +
        (6863 / 10000) * 0.000244040270 * 13101 * 0.000976220636) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002823477139 + 0.000643350796 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13101 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13101 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13101 0.011 Θ ∧ gammaRatio 13101 0.011 Θ ≤ 0.000083894734 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13101 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035252148649 : ℝ) * 0.525 / ((1 - 0.011) * 13101) := by gcongr
      _ ≤ (0.000083894734 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13101 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13101 0.011 Θ) :=
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
    badAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13101 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13101 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13101 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13101 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13101 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13101 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13101 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13101 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13101 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13101 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035252148649 : ℝ) * 13101 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172382721 + 0.003189417222 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13101

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13101
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13101 BstLean.Part154.csC) (piBar (rhoBar 13101 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13101 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13101 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13101 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13101 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13101 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13101 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13101 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13101 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13101 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13101 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051666199293 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13101) ≤ 0.010433703967 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13101 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035252148649)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010433703967 + 2 * 0.737676 / 13101) := by gcongr
    _ ≤ (0.051666199293 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13101 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13101

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13101
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521147637 : ℝ) ≤ plow 13101 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13101) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353426763)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336684874) : eMP 13101 0.011 xi bn ≤ 0.001151288436 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13101 : ℝ) * (1 - 0.011))) ≤ 0.000569297279 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336684874 / (13101 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569297279 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569297279 : ℝ) + 3.141593 * 0.052353426763 / (13101 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151288436 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353426763)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336684874) : PiBarMP 13101 12 0.011 xi bn ≤ 0.158739572942 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13101 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036560701225 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.828331271261 : ℝ) ≤ √((13101 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.459599859513 : ℝ) ≤ √(13101 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13101) ≤ 0.121723370341 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036560701225 + 0.052353426763 * 1.772454 / (2 * (113.828331271261 : ℝ))) * (1 + 0.001151288436) +
        8 / (13101 * 114.459599859513) + 0.121723370341 := by gcongr
    _ ≤ (0.158739572942 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353426763)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336684874) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280474911459) :
    parallelOracle 13101 0.011 xi bn cd ≤ 0.159699628690 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13101 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13101 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521147637 : ℝ) ≤ plow 13101 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.459599859513 : ℝ) ≤ √(13101 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280474911459 : ℝ) / (2 * 0.560521147637 * 114.459599859513)) * 0.158739572942 +
        0.280474911459 ^ 2 / (2 * 0.560521147637 * 114.459599859513) := by gcongr
    _ ≤ (0.159699628690 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353426763) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336684874)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280474911459) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13101 13101 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521147637 : ℝ) ≤ plow 13101 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.459599859513 : ℝ) ≤ √(13101 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13101 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13101 Θ 1.22 ≤ 0.011585751669 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.459599859513 := by gcongr <;> linarith
      _ ≤ (0.011585751669 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13101 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13101 13101 0.011 ≤ 0.008351304022 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13101 13101 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13101 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13101 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13101 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13101 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159699628690 + 0.011585751669 + (0.008351304022 : ℝ) *
        (1 + 2 * (0.280474911459 + 0.011585751669) / (0.560521147637 * 114.459599859513))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13101]

end BstLean.Part269.N13101

/-! The original eight local profiles supply actual 13101 moment certificates. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13101 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052353426763 ∧
    0 ≤ bN 13101 BstLean.Part154.csC (groupTheta g) ∧ bN 13101 BstLean.Part154.csC (groupTheta g) ≤ 0.001336684874 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13101 13101 0.011
      (momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13101 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13101 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13101 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228808712166 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13101 0.011
      (momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13101 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13101
/-! The actual computed-centre upper energy formula at 13101. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13101

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13101)
open BstLean.Part268 (cell13101)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084399629591
  | 2 => 0.085324951601
  | 3 => 0.086245985031
  | 4 => 0.087163576879
  | 5 => 0.088078768001
  | 6 => 0.088992823913
  | 7 => 0.089907268863
  | 8 => 0.090823923305
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13101 13101 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13101 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13101

/-! Actual upper energy certificates on all 43 source endpoints at 13101. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13101)
open BstLean.Part268 (cell13101)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13101 (gMinus 13101) (1 - (cell13101 i).lower) ≤ 1 ∧
    energyUpper 13101 (gMinus 13101) (BstLean.Part211.gPlus 13101)
      (finiteEnergy 13101 13101 0.011) (1 - (cell13101 i).lower) ≤
      (cell13101 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨10,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨11,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨12,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨13,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨14,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨15,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨16,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨17,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨18,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨19,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨20,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨21,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨22,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨23,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨24,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨25,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨26,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨27,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨28,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨29,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨30,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨31,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨32,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨33,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨34,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨35,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨36,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨37,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨38,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨39,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨40,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨41,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨42,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨43,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨44,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨45,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨46,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨47,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨48,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨49,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨50,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨51,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13101) (by norm_num)
        (q := 1 - (cell13101 ⟨52,by decide⟩).lower)
        (by norm_num [cell13101]) (by norm_num [cell13101])
      exact ⟨E.1,E.2.trans (by norm_num [cell13101])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13101

/-! Source-cell containment and simple scalar guards at 13101. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13101)
open BstLean.Part268 (cell13101)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13101 ⟨10,by decide⟩).lower ∧ (cell13101 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13101 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13101 ⟨11,by decide⟩).lower ∧ (cell13101 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13101 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13101 ⟨12,by decide⟩).lower ∧ (cell13101 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13101 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13101 ⟨13,by decide⟩).lower ∧ (cell13101 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13101 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13101 ⟨14,by decide⟩).lower ∧ (cell13101 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13101 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13101 ⟨15,by decide⟩).lower ∧ (cell13101 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13101 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13101 ⟨16,by decide⟩).lower ∧ (cell13101 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13101 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13101 ⟨17,by decide⟩).lower ∧ (cell13101 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13101 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13101 ⟨18,by decide⟩).lower ∧ (cell13101 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13101 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13101 ⟨19,by decide⟩).lower ∧ (cell13101 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13101 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13101 ⟨20,by decide⟩).lower ∧ (cell13101 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13101 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13101 ⟨21,by decide⟩).lower ∧ (cell13101 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13101 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13101 ⟨22,by decide⟩).lower ∧ (cell13101 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13101 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13101 ⟨23,by decide⟩).lower ∧ (cell13101 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13101 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13101 ⟨24,by decide⟩).lower ∧ (cell13101 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13101 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13101 ⟨25,by decide⟩).lower ∧ (cell13101 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13101 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13101 ⟨26,by decide⟩).lower ∧ (cell13101 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13101 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13101 ⟨27,by decide⟩).lower ∧ (cell13101 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13101 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13101 ⟨28,by decide⟩).lower ∧ (cell13101 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13101 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13101 ⟨29,by decide⟩).lower ∧ (cell13101 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13101 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13101 ⟨30,by decide⟩).lower ∧ (cell13101 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13101 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13101 ⟨31,by decide⟩).lower ∧ (cell13101 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13101 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13101 ⟨32,by decide⟩).lower ∧ (cell13101 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13101 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13101 ⟨33,by decide⟩).lower ∧ (cell13101 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13101 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13101 ⟨34,by decide⟩).lower ∧ (cell13101 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13101 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13101 ⟨35,by decide⟩).lower ∧ (cell13101 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13101 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13101 ⟨36,by decide⟩).lower ∧ (cell13101 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13101 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13101 ⟨37,by decide⟩).lower ∧ (cell13101 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13101 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13101 ⟨38,by decide⟩).lower ∧ (cell13101 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13101 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13101 ⟨39,by decide⟩).lower ∧ (cell13101 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13101 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13101 ⟨40,by decide⟩).lower ∧ (cell13101 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13101 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13101 ⟨41,by decide⟩).lower ∧ (cell13101 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13101 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13101 ⟨42,by decide⟩).lower ∧ (cell13101 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13101 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13101 ⟨43,by decide⟩).lower ∧ (cell13101 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13101 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13101 ⟨44,by decide⟩).lower ∧ (cell13101 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13101 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13101 ⟨45,by decide⟩).lower ∧ (cell13101 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13101 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13101 ⟨46,by decide⟩).lower ∧ (cell13101 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13101 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13101 ⟨47,by decide⟩).lower ∧ (cell13101 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13101 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13101 ⟨48,by decide⟩).lower ∧ (cell13101 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13101 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13101 ⟨49,by decide⟩).lower ∧ (cell13101 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13101 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13101 ⟨50,by decide⟩).lower ∧ (cell13101 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13101 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13101 ⟨51,by decide⟩).lower ∧ (cell13101 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13101 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13101 ⟨52,by decide⟩).lower ∧ (cell13101 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13101 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13101 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13101 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13101,cell13101,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13101 i).lower ∧
    (cell13101 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13101 i).upper ≤ (0.532 : ℝ) ∧
    (cell13101 i).centre ≤ (0.1 : ℝ) ∧ (cell13101 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13101 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13101 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13101

/-! The local source numeric instances at 13101 have no network premises. -/
namespace BstLean.Part269.N13101
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13101)
open BstLean.Part268 (cell13101)

noncomputable def sourceNumerics13101 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13101 (cell13101 i)
      scalarRow13101.M scalarRow13101.H scalarRow13101.xi := by
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
    energy_allowance := scalarRow13101.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13101]
    centre_nonneg := (scalarRow13101.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13101])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13101
/-! Actual 13102 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13102 ≤ (1.035250791675 : ℝ) := by
  have hr : (114.463968129713 : ℝ) ≤ √(13102 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.463968129713 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13102 13102 (11 / 1000) ≤
    (0.008350985310 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13102) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.463968129713 : ℝ) ≤ √(13102 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13102)
  have hdiv : K / √(13102 : ℝ) ≤ K / 114.463968129713 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.463968129713 ≤ (0.008350985310 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13102.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13102 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13102 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13102 := gPlus_lower 13102
end BstLean.Part269.N13102

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13102
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035250791674 : ℝ) ≤ wn 13102 := by
  have hn : √(13102 : ℝ) ≤ 114.463968129714 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13102 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.463968129714 ≤ 2 / √(13102 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244020946 : ℝ) ≤ rhoBar 13102 BstLean.Part154.csC ∧
    rhoBar 13102 BstLean.Part154.csC ≤ 0.000244021324 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035250791674 : ℝ) / (1.295212 * 13102) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035250791675 : ℝ) / (1.29521 * 13102) := by gcongr
      _ ≤ (0.000244021324 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13102 BstLean.Part154.csC) ≤ 0.000976144843 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13102 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) ≤ 0.000186384863 ∧
    cc1 (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) ≤ 0.000118597982 ∧
    cc2 (rhoBar 13102 BstLean.Part154.csC) ≤ 0.000068847105 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13102 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13102 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13102 BstLean.Part154.csC * nuR (rhoBar 13102 BstLean.Part154.csC)) ≤ 0.000488057535 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244021324 : ℝ) * 0.000976144843 := by gcongr
      _ ≤ (0.000488057535 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13102 BstLean.Part154.csC) * nuR (rhoBar 13102 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976144843 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13102 BstLean.Part154.csC) * rhoBar 13102 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244021324 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244021324 / 2 + 0.399 * 0.000976144843 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186384863 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488057535 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118597982 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244021324 / 1.414213562 := by gcongr
      _ ≤ (0.000068847105 : ℝ) := by norm_num

end BstLean.Part269.N13102

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13102
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) ≤ 1.50023E-7 := by
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13102 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13102 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13102 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186384863 : ℝ) ^ 2 + 0.000118597982 ^ 2 + 3 * 0.000068847105 ^ 2 +
        2 * 0.797885 * 0.000186384863 * 0.000118597982 + 2 * 0.000186384863 * 0.000068847105 +
        4 * 0.797885 * 0.000118597982 * 0.000068847105 := by gcongr
    _ ≤ (1.50023E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13102 BstLean.Part154.csC Θ ≤ 0.002545870461 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13102 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13102 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13102 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035250791675 * 1.50023E-7 / (0.000244020946 : ℝ) := by gcongr
    _ ≤ 0.002545870461 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13102 BstLean.Part154.csC Θ ≤ 0.002823250526 + 0.000643300006 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13102 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13102 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035250791675 : ℝ) * ((2 * Θ * 0.000244021324 +
        (6863 / 10000) * 0.000244021324 * 13102 * 0.000976144843) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002823250526 + 0.000643300006 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13102 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13102 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13102 0.011 Θ ∧ gammaRatio 13102 0.011 Θ ≤ 0.000083888221 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13102 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035250791675 : ℝ) * 0.525 / ((1 - 0.011) * 13102) := by gcongr
      _ ≤ (0.000083888221 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13102 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13102 0.011 Θ) :=
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
    badAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13102 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13102 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13102 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13102 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13102 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13102 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13102 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13102 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13102 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13102 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035250791675 : ℝ) * 13102 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172156108 + 0.003189170467 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13102

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13102
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13102 BstLean.Part154.csC) (piBar (rhoBar 13102 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13102 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13102 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13102 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13102 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13102 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13102 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13102 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13102 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13102 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13102 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051664206510 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13102) ≤ 0.010433305787 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13102 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035250791675)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010433305787 + 2 * 0.737676 / 13102) := by gcongr
    _ ≤ (0.051664206510 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13102 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13102

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13102
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521190131 : ℝ) ≤ plow 13102 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13102) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353070604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336581993) : eMP 13102 0.011 xi bn ≤ 0.001151200113 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13102 : ℝ) * (1 - 0.011))) ≤ 0.000569253645 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336581993 / (13102 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569253645 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569253645 : ℝ) + 3.141593 * 0.052353070604 / (13102 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151200113 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353070604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336581993) : PiBarMP 13102 12 0.011 xi bn ≤ 0.158733496772 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13102 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036559294209 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.832675449538 : ℝ) ≤ √((13102 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.463968129713 : ℝ) ≤ √(13102 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13102) ≤ 0.121718725032 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036559294209 + 0.052353070604 * 1.772454 / (2 * (113.832675449538 : ℝ))) * (1 + 0.001151200113) +
        8 / (13102 * 114.463968129713) + 0.121718725032 := by gcongr
    _ ≤ (0.158733496772 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353070604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336581993) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280472140385) :
    parallelOracle 13102 0.011 xi bn cd ≤ 0.159693486986 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13102 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13102 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521190131 : ℝ) ≤ plow 13102 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.463968129713 : ℝ) ≤ √(13102 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280472140385 : ℝ) / (2 * 0.560521190131 * 114.463968129713)) * 0.158733496772 +
        0.280472140385 ^ 2 / (2 * 0.560521190131 * 114.463968129713) := by gcongr
    _ ≤ (0.159693486986 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353070604) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336581993)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280472140385) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13102 13102 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521190131 : ℝ) ≤ plow 13102 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.463968129713 : ℝ) ≤ √(13102 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13102 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13102 Θ 1.22 ≤ 0.011585309523 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.463968129713 := by gcongr <;> linarith
      _ ≤ (0.011585309523 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13102 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13102 13102 0.011 ≤ 0.008350985310 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13102 13102 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13102 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13102 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13102 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13102 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159693486986 + 0.011585309523 + (0.008350985310 : ℝ) *
        (1 + 2 * (0.280472140385 + 0.011585309523) / (0.560521190131 * 114.463968129713))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13102]

end BstLean.Part269.N13102

/-! The original eight local profiles supply actual 13102 moment certificates. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13102 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052353070604 ∧
    0 ≤ bN 13102 BstLean.Part154.csC (groupTheta g) ∧ bN 13102 BstLean.Part154.csC (groupTheta g) ≤ 0.001336581993 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13102 13102 0.011
      (momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13102 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13102 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13102 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228807933875 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13102 0.011
      (momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13102 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13102
/-! The actual computed-centre upper energy formula at 13102. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13102

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13102)
open BstLean.Part268 (cell13102)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084397089260
  | 2 => 0.085322379423
  | 3 => 0.086243376401
  | 4 => 0.087160926097
  | 5 => 0.088076068072
  | 6 => 0.088990066312
  | 7 => 0.089904443280
  | 8 => 0.090821017355
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13102 13102 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13102 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13102

/-! Actual upper energy certificates on all 43 source endpoints at 13102. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13102)
open BstLean.Part268 (cell13102)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13102 (gMinus 13102) (1 - (cell13102 i).lower) ≤ 1 ∧
    energyUpper 13102 (gMinus 13102) (BstLean.Part211.gPlus 13102)
      (finiteEnergy 13102 13102 0.011) (1 - (cell13102 i).lower) ≤
      (cell13102 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨10,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨11,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨12,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨13,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨14,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨15,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨16,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨17,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨18,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨19,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨20,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨21,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨22,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨23,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨24,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨25,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨26,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨27,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨28,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨29,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨30,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨31,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨32,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨33,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨34,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨35,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨36,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨37,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨38,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨39,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨40,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨41,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨42,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨43,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨44,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨45,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨46,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨47,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨48,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨49,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨50,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨51,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13102) (by norm_num)
        (q := 1 - (cell13102 ⟨52,by decide⟩).lower)
        (by norm_num [cell13102]) (by norm_num [cell13102])
      exact ⟨E.1,E.2.trans (by norm_num [cell13102])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13102

/-! Source-cell containment and simple scalar guards at 13102. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13102)
open BstLean.Part268 (cell13102)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13102 ⟨10,by decide⟩).lower ∧ (cell13102 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13102 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13102 ⟨11,by decide⟩).lower ∧ (cell13102 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13102 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13102 ⟨12,by decide⟩).lower ∧ (cell13102 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13102 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13102 ⟨13,by decide⟩).lower ∧ (cell13102 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13102 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13102 ⟨14,by decide⟩).lower ∧ (cell13102 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13102 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13102 ⟨15,by decide⟩).lower ∧ (cell13102 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13102 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13102 ⟨16,by decide⟩).lower ∧ (cell13102 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13102 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13102 ⟨17,by decide⟩).lower ∧ (cell13102 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13102 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13102 ⟨18,by decide⟩).lower ∧ (cell13102 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13102 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13102 ⟨19,by decide⟩).lower ∧ (cell13102 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13102 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13102 ⟨20,by decide⟩).lower ∧ (cell13102 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13102 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13102 ⟨21,by decide⟩).lower ∧ (cell13102 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13102 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13102 ⟨22,by decide⟩).lower ∧ (cell13102 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13102 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13102 ⟨23,by decide⟩).lower ∧ (cell13102 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13102 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13102 ⟨24,by decide⟩).lower ∧ (cell13102 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13102 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13102 ⟨25,by decide⟩).lower ∧ (cell13102 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13102 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13102 ⟨26,by decide⟩).lower ∧ (cell13102 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13102 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13102 ⟨27,by decide⟩).lower ∧ (cell13102 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13102 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13102 ⟨28,by decide⟩).lower ∧ (cell13102 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13102 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13102 ⟨29,by decide⟩).lower ∧ (cell13102 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13102 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13102 ⟨30,by decide⟩).lower ∧ (cell13102 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13102 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13102 ⟨31,by decide⟩).lower ∧ (cell13102 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13102 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13102 ⟨32,by decide⟩).lower ∧ (cell13102 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13102 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13102 ⟨33,by decide⟩).lower ∧ (cell13102 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13102 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13102 ⟨34,by decide⟩).lower ∧ (cell13102 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13102 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13102 ⟨35,by decide⟩).lower ∧ (cell13102 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13102 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13102 ⟨36,by decide⟩).lower ∧ (cell13102 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13102 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13102 ⟨37,by decide⟩).lower ∧ (cell13102 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13102 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13102 ⟨38,by decide⟩).lower ∧ (cell13102 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13102 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13102 ⟨39,by decide⟩).lower ∧ (cell13102 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13102 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13102 ⟨40,by decide⟩).lower ∧ (cell13102 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13102 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13102 ⟨41,by decide⟩).lower ∧ (cell13102 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13102 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13102 ⟨42,by decide⟩).lower ∧ (cell13102 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13102 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13102 ⟨43,by decide⟩).lower ∧ (cell13102 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13102 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13102 ⟨44,by decide⟩).lower ∧ (cell13102 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13102 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13102 ⟨45,by decide⟩).lower ∧ (cell13102 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13102 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13102 ⟨46,by decide⟩).lower ∧ (cell13102 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13102 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13102 ⟨47,by decide⟩).lower ∧ (cell13102 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13102 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13102 ⟨48,by decide⟩).lower ∧ (cell13102 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13102 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13102 ⟨49,by decide⟩).lower ∧ (cell13102 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13102 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13102 ⟨50,by decide⟩).lower ∧ (cell13102 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13102 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13102 ⟨51,by decide⟩).lower ∧ (cell13102 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13102 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13102 ⟨52,by decide⟩).lower ∧ (cell13102 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13102 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13102 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13102 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13102,cell13102,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13102 i).lower ∧
    (cell13102 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13102 i).upper ≤ (0.532 : ℝ) ∧
    (cell13102 i).centre ≤ (0.1 : ℝ) ∧ (cell13102 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13102 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13102 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13102

/-! The local source numeric instances at 13102 have no network premises. -/
namespace BstLean.Part269.N13102
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13102)
open BstLean.Part268 (cell13102)

noncomputable def sourceNumerics13102 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13102 (cell13102 i)
      scalarRow13102.M scalarRow13102.H scalarRow13102.xi := by
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
    energy_allowance := scalarRow13102.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13102]
    centre_nonneg := (scalarRow13102.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13102])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13102
/-! Actual 13103 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13103 ≤ (1.035249434858 : ℝ) := by
  have hr : (114.468336233213 : ℝ) ≤ √(13103 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.468336233213 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13103 13103 (11 / 1000) ≤
    (0.008350666635 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13103) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.468336233213 : ℝ) ≤ √(13103 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13103)
  have hdiv : K / √(13103 : ℝ) ≤ K / 114.468336233213 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.468336233213 ≤ (0.008350666635 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13103.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13103 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13103 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13103 := gPlus_lower 13103
end BstLean.Part269.N13103

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13103
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035249434857 : ℝ) ≤ wn 13103 := by
  have hn : √(13103 : ℝ) ≤ 114.468336233214 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13103 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.468336233214 ≤ 2 / √(13103 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244002003 : ℝ) ≤ rhoBar 13103 BstLean.Part154.csC ∧
    rhoBar 13103 BstLean.Part154.csC ≤ 0.000244002381 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035249434857 : ℝ) / (1.295212 * 13103) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035249434858 : ℝ) / (1.29521 * 13103) := by gcongr
      _ ≤ (0.000244002381 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13103 BstLean.Part154.csC) ≤ 0.000976069062 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13103 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) ≤ 0.000186370394 ∧
    cc1 (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) ≤ 0.000118588775 ∧
    cc2 (rhoBar 13103 BstLean.Part154.csC) ≤ 0.000068841760 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13103 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13103 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13103 BstLean.Part154.csC * nuR (rhoBar 13103 BstLean.Part154.csC)) ≤ 0.000488019647 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244002381 : ℝ) * 0.000976069062 := by gcongr
      _ ≤ (0.000488019647 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13103 BstLean.Part154.csC) * nuR (rhoBar 13103 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976069062 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13103 BstLean.Part154.csC) * rhoBar 13103 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244002381 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244002381 / 2 + 0.399 * 0.000976069062 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186370394 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488019647 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118588775 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244002381 / 1.414213562 := by gcongr
      _ ≤ (0.000068841760 : ℝ) := by norm_num

end BstLean.Part269.N13103

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13103
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) ≤ 1.50000E-7 := by
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13103 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13103 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13103 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186370394 : ℝ) ^ 2 + 0.000118588775 ^ 2 + 3 * 0.000068841760 ^ 2 +
        2 * 0.797885 * 0.000186370394 * 0.000118588775 + 2 * 0.000186370394 * 0.000068841760 +
        4 * 0.797885 * 0.000118588775 * 0.000068841760 := by gcongr
    _ ≤ (1.50000E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13103 BstLean.Part154.csC Θ ≤ 0.002545674435 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13103 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13103 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13103 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035249434858 * 1.50000E-7 / (0.000244002003 : ℝ) := by gcongr
    _ ≤ 0.002545674435 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13103 BstLean.Part154.csC Θ ≤ 0.002823023950 + 0.000643249225 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13103 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13103 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035249434858 : ℝ) * ((2 * Θ * 0.000244002381 +
        (6863 / 10000) * 0.000244002381 * 13103 * 0.000976069062) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002823023950 + 0.000643249225 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13103 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13103 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13103 0.011 Θ ∧ gammaRatio 13103 0.011 Θ ≤ 0.000083881709 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13103 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035249434858 : ℝ) * 0.525 / ((1 - 0.011) * 13103) := by gcongr
      _ ≤ (0.000083881709 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13103 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13103 0.011 Θ) :=
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
    badAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13103 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13103 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13103 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13103 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13103 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13103 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13103 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13103 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13103 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13103 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035249434858 : ℝ) * 13103 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003171929532 + 0.003188923660 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13103

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13103
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13103 BstLean.Part154.csC) (piBar (rhoBar 13103 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13103 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13103 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13103 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13103 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13103 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13103 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13103 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13103 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13103 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13103 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051662213959 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13103) ≤ 0.010432907653 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13103 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035249434858)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010432907653 + 2 * 0.737676 / 13103) := by gcongr
    _ ≤ (0.051662213959 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13103 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13103

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13103
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521232618 : ℝ) ≤ plow 13103 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13103) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352714454)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336479079) : eMP 13103 0.011 xi bn ≤ 0.001151111782 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13103 : ℝ) * (1 - 0.011))) ≤ 0.000569210007 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336479079 / (13103 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569210007 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569210007 : ℝ) + 3.141593 * 0.052352714454 / (13103 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151111782 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352714454)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336479079) : PiBarMP 13103 12 0.011 xi bn ≤ 0.158727420629 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13103 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036557886687 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.837019462036 : ℝ) ≤ √((13103 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.468336233213 : ℝ) ≤ √(13103 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13103) ≤ 0.121714080254 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036557886687 + 0.052352714454 * 1.772454 / (2 * (113.837019462036 : ℝ))) * (1 + 0.001151111782) +
        8 / (13103 * 114.468336233213) + 0.121714080254 := by gcongr
    _ ≤ (0.158727420629 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352714454)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336479079) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280469369560) :
    parallelOracle 13103 0.011 xi bn cd ≤ 0.159687345317 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13103 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13103 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521232618 : ℝ) ≤ plow 13103 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.468336233213 : ℝ) ≤ √(13103 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280469369560 : ℝ) / (2 * 0.560521232618 * 114.468336233213)) * 0.158727420629 +
        0.280469369560 ^ 2 / (2 * 0.560521232618 * 114.468336233213) := by gcongr
    _ ≤ (0.159687345317 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352714454) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336479079)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280469369560) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13103 13103 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521232618 : ℝ) ≤ plow 13103 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.468336233213 : ℝ) ≤ √(13103 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13103 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13103 Θ 1.22 ≤ 0.011584867429 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.468336233213 := by gcongr <;> linarith
      _ ≤ (0.011584867429 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13103 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13103 13103 0.011 ≤ 0.008350666635 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13103 13103 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13103 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13103 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13103 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13103 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159687345317 + 0.011584867429 + (0.008350666635 : ℝ) *
        (1 + 2 * (0.280469369560 + 0.011584867429) / (0.560521232618 * 114.468336233213))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13103]

end BstLean.Part269.N13103

/-! The original eight local profiles supply actual 13103 moment certificates. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13103 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052352714454 ∧
    0 ≤ bN 13103 BstLean.Part154.csC (groupTheta g) ∧ bN 13103 BstLean.Part154.csC (groupTheta g) ≤ 0.001336479079 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13103 13103 0.011
      (momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13103 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13103 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13103 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228807155601 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13103 0.011
      (momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13103 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13103
/-! The actual computed-centre upper energy formula at 13103. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13103

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13103)
open BstLean.Part268 (cell13103)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084394549665
  | 2 => 0.085319808006
  | 3 => 0.086240768563
  | 4 => 0.087158276147
  | 5 => 0.088073369020
  | 6 => 0.088987309646
  | 7 => 0.089901618703
  | 8 => 0.090818112494
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13103 13103 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13103 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13103

/-! Actual upper energy certificates on all 43 source endpoints at 13103. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13103)
open BstLean.Part268 (cell13103)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13103 (gMinus 13103) (1 - (cell13103 i).lower) ≤ 1 ∧
    energyUpper 13103 (gMinus 13103) (BstLean.Part211.gPlus 13103)
      (finiteEnergy 13103 13103 0.011) (1 - (cell13103 i).lower) ≤
      (cell13103 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨10,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨11,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨12,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨13,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨14,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨15,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨16,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨17,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨18,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨19,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨20,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨21,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨22,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨23,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨24,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨25,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨26,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨27,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨28,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨29,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨30,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨31,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨32,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨33,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨34,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨35,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨36,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨37,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨38,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨39,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨40,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨41,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨42,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨43,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨44,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨45,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨46,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨47,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨48,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨49,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨50,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨51,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13103) (by norm_num)
        (q := 1 - (cell13103 ⟨52,by decide⟩).lower)
        (by norm_num [cell13103]) (by norm_num [cell13103])
      exact ⟨E.1,E.2.trans (by norm_num [cell13103])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13103

/-! Source-cell containment and simple scalar guards at 13103. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13103)
open BstLean.Part268 (cell13103)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13103 ⟨10,by decide⟩).lower ∧ (cell13103 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13103 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13103 ⟨11,by decide⟩).lower ∧ (cell13103 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13103 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13103 ⟨12,by decide⟩).lower ∧ (cell13103 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13103 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13103 ⟨13,by decide⟩).lower ∧ (cell13103 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13103 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13103 ⟨14,by decide⟩).lower ∧ (cell13103 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13103 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13103 ⟨15,by decide⟩).lower ∧ (cell13103 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13103 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13103 ⟨16,by decide⟩).lower ∧ (cell13103 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13103 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13103 ⟨17,by decide⟩).lower ∧ (cell13103 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13103 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13103 ⟨18,by decide⟩).lower ∧ (cell13103 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13103 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13103 ⟨19,by decide⟩).lower ∧ (cell13103 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13103 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13103 ⟨20,by decide⟩).lower ∧ (cell13103 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13103 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13103 ⟨21,by decide⟩).lower ∧ (cell13103 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13103 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13103 ⟨22,by decide⟩).lower ∧ (cell13103 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13103 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13103 ⟨23,by decide⟩).lower ∧ (cell13103 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13103 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13103 ⟨24,by decide⟩).lower ∧ (cell13103 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13103 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13103 ⟨25,by decide⟩).lower ∧ (cell13103 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13103 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13103 ⟨26,by decide⟩).lower ∧ (cell13103 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13103 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13103 ⟨27,by decide⟩).lower ∧ (cell13103 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13103 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13103 ⟨28,by decide⟩).lower ∧ (cell13103 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13103 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13103 ⟨29,by decide⟩).lower ∧ (cell13103 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13103 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13103 ⟨30,by decide⟩).lower ∧ (cell13103 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13103 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13103 ⟨31,by decide⟩).lower ∧ (cell13103 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13103 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13103 ⟨32,by decide⟩).lower ∧ (cell13103 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13103 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13103 ⟨33,by decide⟩).lower ∧ (cell13103 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13103 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13103 ⟨34,by decide⟩).lower ∧ (cell13103 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13103 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13103 ⟨35,by decide⟩).lower ∧ (cell13103 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13103 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13103 ⟨36,by decide⟩).lower ∧ (cell13103 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13103 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13103 ⟨37,by decide⟩).lower ∧ (cell13103 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13103 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13103 ⟨38,by decide⟩).lower ∧ (cell13103 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13103 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13103 ⟨39,by decide⟩).lower ∧ (cell13103 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13103 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13103 ⟨40,by decide⟩).lower ∧ (cell13103 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13103 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13103 ⟨41,by decide⟩).lower ∧ (cell13103 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13103 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13103 ⟨42,by decide⟩).lower ∧ (cell13103 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13103 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13103 ⟨43,by decide⟩).lower ∧ (cell13103 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13103 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13103 ⟨44,by decide⟩).lower ∧ (cell13103 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13103 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13103 ⟨45,by decide⟩).lower ∧ (cell13103 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13103 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13103 ⟨46,by decide⟩).lower ∧ (cell13103 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13103 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13103 ⟨47,by decide⟩).lower ∧ (cell13103 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13103 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13103 ⟨48,by decide⟩).lower ∧ (cell13103 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13103 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13103 ⟨49,by decide⟩).lower ∧ (cell13103 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13103 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13103 ⟨50,by decide⟩).lower ∧ (cell13103 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13103 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13103 ⟨51,by decide⟩).lower ∧ (cell13103 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13103 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13103 ⟨52,by decide⟩).lower ∧ (cell13103 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13103 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13103 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13103 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13103,cell13103,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13103 i).lower ∧
    (cell13103 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13103 i).upper ≤ (0.532 : ℝ) ∧
    (cell13103 i).centre ≤ (0.1 : ℝ) ∧ (cell13103 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13103 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13103 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13103

/-! The local source numeric instances at 13103 have no network premises. -/
namespace BstLean.Part269.N13103
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13103)
open BstLean.Part268 (cell13103)

noncomputable def sourceNumerics13103 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13103 (cell13103 i)
      scalarRow13103.M scalarRow13103.H scalarRow13103.xi := by
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
    energy_allowance := scalarRow13103.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13103]
    centre_nonneg := (scalarRow13103.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13103])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13103
/-! Actual 13104 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13104 ≤ (1.035248078196 : ℝ) := by
  have hr : (114.472704170033 : ℝ) ≤ √(13104 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.472704170033 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13104 13104 (11 / 1000) ≤
    (0.008350347996 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13104) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.472704170033 : ℝ) ≤ √(13104 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13104)
  have hdiv : K / √(13104 : ℝ) ≤ K / 114.472704170033 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.472704170033 ≤ (0.008350347996 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13104.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13104 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13104 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13104 := gPlus_lower 13104
end BstLean.Part269.N13104

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13104
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035248078195 : ℝ) ≤ wn 13104 := by
  have hn : √(13104 : ℝ) ≤ 114.472704170034 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13104 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.472704170034 ≤ 2 / √(13104 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243983063 : ℝ) ≤ rhoBar 13104 BstLean.Part154.csC ∧
    rhoBar 13104 BstLean.Part154.csC ≤ 0.000243983441 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035248078195 : ℝ) / (1.295212 * 13104) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035248078196 : ℝ) / (1.29521 * 13104) := by gcongr
      _ ≤ (0.000243983441 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13104 BstLean.Part154.csC) ≤ 0.000975993292 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13104 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) ≤ 0.000186355926 ∧
    cc1 (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) ≤ 0.000118579569 ∧
    cc2 (rhoBar 13104 BstLean.Part154.csC) ≤ 0.000068836416 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13104 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13104 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13104 BstLean.Part154.csC * nuR (rhoBar 13104 BstLean.Part154.csC)) ≤ 0.000487981764 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243983441 : ℝ) * 0.000975993292 := by gcongr
      _ ≤ (0.000487981764 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13104 BstLean.Part154.csC) * nuR (rhoBar 13104 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975993292 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13104 BstLean.Part154.csC) * rhoBar 13104 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243983441 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243983441 / 2 + 0.399 * 0.000975993292 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186355926 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487981764 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118579569 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243983441 / 1.414213562 := by gcongr
      _ ≤ (0.000068836416 : ℝ) := by norm_num

end BstLean.Part269.N13104

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13104
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) ≤ 1.49976E-7 := by
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13104 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13104 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13104 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186355926 : ℝ) ^ 2 + 0.000118579569 ^ 2 + 3 * 0.000068836416 ^ 2 +
        2 * 0.797885 * 0.000186355926 * 0.000118579569 + 2 * 0.000186355926 * 0.000068836416 +
        4 * 0.797885 * 0.000118579569 * 0.000068836416 := by gcongr
    _ ≤ (1.49976E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13104 BstLean.Part154.csC Θ ≤ 0.002545461376 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13104 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13104 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13104 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035248078196 * 1.49976E-7 / (0.000243983063 : ℝ) := by gcongr
    _ ≤ 0.002545461376 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13104 BstLean.Part154.csC Θ ≤ 0.002822797409 + 0.000643198451 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13104 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13104 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035248078196 : ℝ) * ((2 * Θ * 0.000243983441 +
        (6863 / 10000) * 0.000243983441 * 13104 * 0.000975993292) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002822797409 + 0.000643198451 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13104 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13104 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13104 0.011 Θ ∧ gammaRatio 13104 0.011 Θ ≤ 0.000083875198 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13104 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035248078196 : ℝ) * 0.525 / ((1 - 0.011) * 13104) := by gcongr
      _ ≤ (0.000083875198 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13104 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13104 0.011 Θ) :=
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
    badAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13104 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13104 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13104 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13104 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13104 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13104 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13104 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13104 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13104 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13104 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035248078196 : ℝ) * 13104 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003171702991 + 0.003188659827 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13104

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13104
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13104 BstLean.Part154.csC) (piBar (rhoBar 13104 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13104 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13104 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13104 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13104 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13104 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13104 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13104 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13104 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13104 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13104 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051660221634 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13104) ≤ 0.010432509564 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13104 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035248078196)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010432509564 + 2 * 0.737676 / 13104) := by gcongr
    _ ≤ (0.051660221634 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13104 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13104

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13104
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521275099 : ℝ) ≤ plow 13104 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13104) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352349401)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336367223) : eMP 13104 0.011 xi bn ≤ 0.001151019647 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13104 : ℝ) * (1 - 0.011))) ≤ 0.000569164468 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336367223 / (13104 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569164468 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569164468 : ℝ) + 3.141593 * 0.052352349401 / (13104 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151019647 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352349401)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336367223) : PiBarMP 13104 12 0.011 xi bn ≤ 0.158721222311 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13104 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036556356807 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.841363308772 : ℝ) ≤ √((13104 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.472704170033 : ℝ) ≤ √(13104 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13104) ≤ 0.121709436008 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036556356807 + 0.052352349401 * 1.772454 / (2 * (113.841363308772 : ℝ))) * (1 + 0.001151019647) +
        8 / (13104 * 114.472704170033) + 0.121709436008 := by gcongr
    _ ≤ (0.158721222311 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352349401)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336367223) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280466579503) :
    parallelOracle 13104 0.011 xi bn cd ≤ 0.159681081106 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13104 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13104 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521275099 : ℝ) ≤ plow 13104 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.472704170033 : ℝ) ≤ √(13104 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280466579503 : ℝ) / (2 * 0.560521275099 * 114.472704170033)) * 0.158721222311 +
        0.280466579503 ^ 2 / (2 * 0.560521275099 * 114.472704170033) := by gcongr
    _ ≤ (0.159681081106 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052352349401) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336367223)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280466579503) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13104 13104 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521275099 : ℝ) ≤ plow 13104 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.472704170033 : ℝ) ≤ √(13104 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13104 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13104 Θ 1.22 ≤ 0.011584425385 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.472704170033 := by gcongr <;> linarith
      _ ≤ (0.011584425385 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13104 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13104 13104 0.011 ≤ 0.008350347996 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13104 13104 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13104 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13104 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13104 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13104 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159681081106 + 0.011584425385 + (0.008350347996 : ℝ) *
        (1 + 2 * (0.280466579503 + 0.011584425385) / (0.560521275099 * 114.472704170033))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13104]

end BstLean.Part269.N13104

/-! The original eight local profiles supply actual 13104 moment certificates. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13104 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052352349401 ∧
    0 ≤ bN 13104 BstLean.Part154.csC (groupTheta g) ∧ bN 13104 BstLean.Part154.csC (groupTheta g) ≤ 0.001336367223 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13104 13104 0.011
      (momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13104 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13104 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13104 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228806357869 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13104 0.011
      (momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13104 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13104
/-! The actual computed-centre upper energy formula at 13104. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13104

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13104)
open BstLean.Part268 (cell13104)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084392010805
  | 2 => 0.085317237349
  | 3 => 0.086238161517
  | 4 => 0.087155627026
  | 5 => 0.088070670846
  | 6 => 0.088984553915
  | 7 => 0.089898795130
  | 8 => 0.090815208723
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13104 13104 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13104 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13104

/-! Actual upper energy certificates on all 43 source endpoints at 13104. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13104)
open BstLean.Part268 (cell13104)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13104 (gMinus 13104) (1 - (cell13104 i).lower) ≤ 1 ∧
    energyUpper 13104 (gMinus 13104) (BstLean.Part211.gPlus 13104)
      (finiteEnergy 13104 13104 0.011) (1 - (cell13104 i).lower) ≤
      (cell13104 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨10,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨11,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨12,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨13,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨14,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨15,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨16,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨17,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨18,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨19,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨20,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨21,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨22,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨23,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨24,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨25,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨26,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨27,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨28,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨29,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨30,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨31,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨32,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨33,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨34,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨35,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨36,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨37,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨38,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨39,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨40,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨41,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨42,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨43,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨44,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨45,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨46,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨47,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨48,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨49,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨50,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨51,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13104) (by norm_num)
        (q := 1 - (cell13104 ⟨52,by decide⟩).lower)
        (by norm_num [cell13104]) (by norm_num [cell13104])
      exact ⟨E.1,E.2.trans (by norm_num [cell13104])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13104

/-! Source-cell containment and simple scalar guards at 13104. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13104)
open BstLean.Part268 (cell13104)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13104 ⟨10,by decide⟩).lower ∧ (cell13104 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13104 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13104 ⟨11,by decide⟩).lower ∧ (cell13104 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13104 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13104 ⟨12,by decide⟩).lower ∧ (cell13104 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13104 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13104 ⟨13,by decide⟩).lower ∧ (cell13104 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13104 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13104 ⟨14,by decide⟩).lower ∧ (cell13104 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13104 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13104 ⟨15,by decide⟩).lower ∧ (cell13104 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13104 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13104 ⟨16,by decide⟩).lower ∧ (cell13104 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13104 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13104 ⟨17,by decide⟩).lower ∧ (cell13104 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13104 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13104 ⟨18,by decide⟩).lower ∧ (cell13104 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13104 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13104 ⟨19,by decide⟩).lower ∧ (cell13104 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13104 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13104 ⟨20,by decide⟩).lower ∧ (cell13104 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13104 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13104 ⟨21,by decide⟩).lower ∧ (cell13104 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13104 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13104 ⟨22,by decide⟩).lower ∧ (cell13104 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13104 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13104 ⟨23,by decide⟩).lower ∧ (cell13104 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13104 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13104 ⟨24,by decide⟩).lower ∧ (cell13104 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13104 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13104 ⟨25,by decide⟩).lower ∧ (cell13104 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13104 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13104 ⟨26,by decide⟩).lower ∧ (cell13104 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13104 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13104 ⟨27,by decide⟩).lower ∧ (cell13104 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13104 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13104 ⟨28,by decide⟩).lower ∧ (cell13104 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13104 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13104 ⟨29,by decide⟩).lower ∧ (cell13104 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13104 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13104 ⟨30,by decide⟩).lower ∧ (cell13104 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13104 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13104 ⟨31,by decide⟩).lower ∧ (cell13104 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13104 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13104 ⟨32,by decide⟩).lower ∧ (cell13104 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13104 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13104 ⟨33,by decide⟩).lower ∧ (cell13104 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13104 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13104 ⟨34,by decide⟩).lower ∧ (cell13104 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13104 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13104 ⟨35,by decide⟩).lower ∧ (cell13104 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13104 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13104 ⟨36,by decide⟩).lower ∧ (cell13104 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13104 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13104 ⟨37,by decide⟩).lower ∧ (cell13104 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13104 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13104 ⟨38,by decide⟩).lower ∧ (cell13104 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13104 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13104 ⟨39,by decide⟩).lower ∧ (cell13104 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13104 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13104 ⟨40,by decide⟩).lower ∧ (cell13104 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13104 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13104 ⟨41,by decide⟩).lower ∧ (cell13104 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13104 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13104 ⟨42,by decide⟩).lower ∧ (cell13104 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13104 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13104 ⟨43,by decide⟩).lower ∧ (cell13104 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13104 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13104 ⟨44,by decide⟩).lower ∧ (cell13104 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13104 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13104 ⟨45,by decide⟩).lower ∧ (cell13104 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13104 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13104 ⟨46,by decide⟩).lower ∧ (cell13104 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13104 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13104 ⟨47,by decide⟩).lower ∧ (cell13104 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13104 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13104 ⟨48,by decide⟩).lower ∧ (cell13104 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13104 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13104 ⟨49,by decide⟩).lower ∧ (cell13104 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13104 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13104 ⟨50,by decide⟩).lower ∧ (cell13104 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13104 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13104 ⟨51,by decide⟩).lower ∧ (cell13104 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13104 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13104 ⟨52,by decide⟩).lower ∧ (cell13104 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13104 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13104 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13104 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13104,cell13104,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13104 i).lower ∧
    (cell13104 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13104 i).upper ≤ (0.532 : ℝ) ∧
    (cell13104 i).centre ≤ (0.1 : ℝ) ∧ (cell13104 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13104 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13104 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13104

/-! The local source numeric instances at 13104 have no network premises. -/
namespace BstLean.Part269.N13104
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13104)
open BstLean.Part268 (cell13104)

noncomputable def sourceNumerics13104 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13104 (cell13104 i)
      scalarRow13104.M scalarRow13104.H scalarRow13104.xi := by
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
    energy_allowance := scalarRow13104.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13104]
    centre_nonneg := (scalarRow13104.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13104])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13104
/-! Actual 13105 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13105 ≤ (1.035246721692 : ℝ) := by
  have hr : (114.477071940192 : ℝ) ≤ √(13105 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.477071940192 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13105 13105 (11 / 1000) ≤
    (0.008350029393 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13105) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.477071940192 : ℝ) ≤ √(13105 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13105)
  have hdiv : K / √(13105 : ℝ) ≤ K / 114.477071940192 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.477071940192 ≤ (0.008350029393 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13105.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13105 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13105 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13105 := gPlus_lower 13105
end BstLean.Part269.N13105

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13105
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035246721691 : ℝ) ≤ wn 13105 := by
  have hn : √(13105 : ℝ) ≤ 114.477071940193 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13105 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.477071940193 ≤ 2 / √(13105 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243964126 : ℝ) ≤ rhoBar 13105 BstLean.Part154.csC ∧
    rhoBar 13105 BstLean.Part154.csC ≤ 0.000243964504 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035246721691 : ℝ) / (1.295212 * 13105) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035246721692 : ℝ) / (1.29521 * 13105) := by gcongr
      _ ≤ (0.000243964504 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13105 BstLean.Part154.csC) ≤ 0.000975917535 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13105 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) ≤ 0.000186341462 ∧
    cc1 (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) ≤ 0.000118570365 ∧
    cc2 (rhoBar 13105 BstLean.Part154.csC) ≤ 0.000068831074 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13105 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13105 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13105 BstLean.Part154.csC * nuR (rhoBar 13105 BstLean.Part154.csC)) ≤ 0.000487943888 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243964504 : ℝ) * 0.000975917535 := by gcongr
      _ ≤ (0.000487943888 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13105 BstLean.Part154.csC) * nuR (rhoBar 13105 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975917535 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13105 BstLean.Part154.csC) * rhoBar 13105 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243964504 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243964504 / 2 + 0.399 * 0.000975917535 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186341462 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487943888 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118570365 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243964504 / 1.414213562 := by gcongr
      _ ≤ (0.000068831074 : ℝ) := by norm_num

end BstLean.Part269.N13105

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13105
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) ≤ 1.49953E-7 := by
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13105 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13105 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13105 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186341462 : ℝ) ^ 2 + 0.000118570365 ^ 2 + 3 * 0.000068831074 ^ 2 +
        2 * 0.797885 * 0.000186341462 * 0.000118570365 + 2 * 0.000186341462 * 0.000068831074 +
        4 * 0.797885 * 0.000118570365 * 0.000068831074 := by gcongr
    _ ≤ (1.49953E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13105 BstLean.Part154.csC Θ ≤ 0.002545265228 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13105 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13105 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13105 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035246721692 * 1.49953E-7 / (0.000243964126 : ℝ) := by gcongr
    _ ≤ 0.002545265228 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13105 BstLean.Part154.csC Θ ≤ 0.002822570908 + 0.000643147686 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13105 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13105 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035246721692 : ℝ) * ((2 * Θ * 0.000243964504 +
        (6863 / 10000) * 0.000243964504 * 13105 * 0.000975917535) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002822570908 + 0.000643147686 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13105 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13105 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13105 0.011 Θ ∧ gammaRatio 13105 0.011 Θ ≤ 0.000083868688 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13105 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035246721692 : ℝ) * 0.525 / ((1 - 0.011) * 13105) := by gcongr
      _ ≤ (0.000083868688 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13105 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13105 0.011 Θ) :=
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
    badAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13105 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13105 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13105 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13105 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13105 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13105 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13105 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13105 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13105 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13105 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035246721692 : ℝ) * 13105 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003171476490 + 0.003188412914 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13105

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13105
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13105 BstLean.Part154.csC) (piBar (rhoBar 13105 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13105 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13105 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13105 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13105 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13105 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13105 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13105 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13105 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13105 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13105 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051658229541 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13105) ≤ 0.010432111521 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13105 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035246721692)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010432111521 + 2 * 0.737676 / 13105) := by gcongr
    _ ≤ (0.051658229541 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13105 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13105

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13105
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521317573 : ℝ) ≤ plow 13105 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13105) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351993270)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336264245) : eMP 13105 0.011 xi bn ≤ 0.001150931302 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13105 : ℝ) * (1 - 0.011))) ≤ 0.000569120823 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336264245 / (13105 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569120823 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569120823 : ℝ) + 3.141593 * 0.052351993270 / (13105 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150931302 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351993270)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336264245) : PiBarMP 13105 12 0.011 xi bn ≤ 0.158715146246 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13105 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036554948298 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.845706989767 : ℝ) ≤ √((13105 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.477071940192 : ℝ) ≤ √(13105 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13105) ≤ 0.121704792293 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036554948298 + 0.052351993270 * 1.772454 / (2 * (113.845706989767 : ℝ))) * (1 + 0.001150931302) +
        8 / (13105 * 114.477071940192) + 0.121704792293 := by gcongr
    _ ≤ (0.158715146246 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351993270)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336264245) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280463809172) :
    parallelOracle 13105 0.011 xi bn cd ≤ 0.159674939531 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13105 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13105 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521317573 : ℝ) ≤ plow 13105 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.477071940192 : ℝ) ≤ √(13105 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280463809172 : ℝ) / (2 * 0.560521317573 * 114.477071940192)) * 0.158715146246 +
        0.280463809172 ^ 2 / (2 * 0.560521317573 * 114.477071940192) := by gcongr
    _ ≤ (0.159674939531 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351993270) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336264245)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280463809172) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13105 13105 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521317573 : ℝ) ≤ plow 13105 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.477071940192 : ℝ) ≤ √(13105 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13105 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13105 Θ 1.22 ≤ 0.011583983391 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.477071940192 := by gcongr <;> linarith
      _ ≤ (0.011583983391 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13105 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13105 13105 0.011 ≤ 0.008350029393 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13105 13105 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13105 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13105 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13105 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13105 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159674939531 + 0.011583983391 + (0.008350029393 : ℝ) *
        (1 + 2 * (0.280463809172 + 0.011583983391) / (0.560521317573 * 114.477071940192))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13105]

end BstLean.Part269.N13105

/-! The original eight local profiles supply actual 13105 moment certificates. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13105 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052351993270 ∧
    0 ≤ bN 13105 BstLean.Part154.csC (groupTheta g) ∧ bN 13105 BstLean.Part154.csC (groupTheta g) ≤ 0.001336264245 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13105 13105 0.011
      (momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13105 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13105 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13105 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228805579631 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13105 0.011
      (momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13105 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13105
/-! The actual computed-centre upper energy formula at 13105. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13105

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13105)
open BstLean.Part268 (cell13105)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084389472680
  | 2 => 0.085314667452
  | 3 => 0.086235555261
  | 4 => 0.087152978734
  | 5 => 0.088067973547
  | 6 => 0.088981799118
  | 7 => 0.089895972561
  | 8 => 0.090812306040
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13105 13105 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13105 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13105

/-! Actual upper energy certificates on all 43 source endpoints at 13105. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13105)
open BstLean.Part268 (cell13105)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13105 (gMinus 13105) (1 - (cell13105 i).lower) ≤ 1 ∧
    energyUpper 13105 (gMinus 13105) (BstLean.Part211.gPlus 13105)
      (finiteEnergy 13105 13105 0.011) (1 - (cell13105 i).lower) ≤
      (cell13105 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨10,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨11,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨12,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨13,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨14,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨15,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨16,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨17,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨18,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨19,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨20,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨21,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨22,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨23,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨24,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨25,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨26,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨27,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨28,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨29,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨30,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨31,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨32,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨33,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨34,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨35,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨36,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨37,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨38,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨39,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨40,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨41,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨42,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨43,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨44,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨45,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨46,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨47,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨48,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨49,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨50,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨51,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13105) (by norm_num)
        (q := 1 - (cell13105 ⟨52,by decide⟩).lower)
        (by norm_num [cell13105]) (by norm_num [cell13105])
      exact ⟨E.1,E.2.trans (by norm_num [cell13105])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13105

/-! Source-cell containment and simple scalar guards at 13105. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13105)
open BstLean.Part268 (cell13105)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13105 ⟨10,by decide⟩).lower ∧ (cell13105 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13105 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13105 ⟨11,by decide⟩).lower ∧ (cell13105 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13105 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13105 ⟨12,by decide⟩).lower ∧ (cell13105 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13105 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13105 ⟨13,by decide⟩).lower ∧ (cell13105 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13105 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13105 ⟨14,by decide⟩).lower ∧ (cell13105 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13105 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13105 ⟨15,by decide⟩).lower ∧ (cell13105 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13105 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13105 ⟨16,by decide⟩).lower ∧ (cell13105 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13105 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13105 ⟨17,by decide⟩).lower ∧ (cell13105 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13105 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13105 ⟨18,by decide⟩).lower ∧ (cell13105 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13105 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13105 ⟨19,by decide⟩).lower ∧ (cell13105 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13105 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13105 ⟨20,by decide⟩).lower ∧ (cell13105 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13105 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13105 ⟨21,by decide⟩).lower ∧ (cell13105 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13105 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13105 ⟨22,by decide⟩).lower ∧ (cell13105 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13105 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13105 ⟨23,by decide⟩).lower ∧ (cell13105 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13105 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13105 ⟨24,by decide⟩).lower ∧ (cell13105 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13105 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13105 ⟨25,by decide⟩).lower ∧ (cell13105 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13105 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13105 ⟨26,by decide⟩).lower ∧ (cell13105 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13105 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13105 ⟨27,by decide⟩).lower ∧ (cell13105 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13105 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13105 ⟨28,by decide⟩).lower ∧ (cell13105 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13105 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13105 ⟨29,by decide⟩).lower ∧ (cell13105 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13105 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13105 ⟨30,by decide⟩).lower ∧ (cell13105 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13105 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13105 ⟨31,by decide⟩).lower ∧ (cell13105 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13105 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13105 ⟨32,by decide⟩).lower ∧ (cell13105 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13105 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13105 ⟨33,by decide⟩).lower ∧ (cell13105 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13105 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13105 ⟨34,by decide⟩).lower ∧ (cell13105 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13105 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13105 ⟨35,by decide⟩).lower ∧ (cell13105 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13105 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13105 ⟨36,by decide⟩).lower ∧ (cell13105 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13105 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13105 ⟨37,by decide⟩).lower ∧ (cell13105 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13105 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13105 ⟨38,by decide⟩).lower ∧ (cell13105 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13105 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13105 ⟨39,by decide⟩).lower ∧ (cell13105 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13105 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13105 ⟨40,by decide⟩).lower ∧ (cell13105 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13105 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13105 ⟨41,by decide⟩).lower ∧ (cell13105 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13105 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13105 ⟨42,by decide⟩).lower ∧ (cell13105 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13105 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13105 ⟨43,by decide⟩).lower ∧ (cell13105 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13105 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13105 ⟨44,by decide⟩).lower ∧ (cell13105 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13105 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13105 ⟨45,by decide⟩).lower ∧ (cell13105 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13105 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13105 ⟨46,by decide⟩).lower ∧ (cell13105 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13105 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13105 ⟨47,by decide⟩).lower ∧ (cell13105 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13105 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13105 ⟨48,by decide⟩).lower ∧ (cell13105 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13105 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13105 ⟨49,by decide⟩).lower ∧ (cell13105 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13105 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13105 ⟨50,by decide⟩).lower ∧ (cell13105 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13105 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13105 ⟨51,by decide⟩).lower ∧ (cell13105 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13105 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13105 ⟨52,by decide⟩).lower ∧ (cell13105 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13105 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13105 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13105 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13105,cell13105,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13105 i).lower ∧
    (cell13105 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13105 i).upper ≤ (0.532 : ℝ) ∧
    (cell13105 i).centre ≤ (0.1 : ℝ) ∧ (cell13105 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13105 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13105 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13105

/-! The local source numeric instances at 13105 have no network premises. -/
namespace BstLean.Part269.N13105
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13105)
open BstLean.Part268 (cell13105)

noncomputable def sourceNumerics13105 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13105 (cell13105 i)
      scalarRow13105.M scalarRow13105.H scalarRow13105.xi := by
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
    energy_allowance := scalarRow13105.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13105]
    centre_nonneg := (scalarRow13105.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13105])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13105
/-! Actual 13106 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13106 ≤ (1.035245365343 : ℝ) := by
  have hr : (114.481439543709 : ℝ) ≤ √(13106 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.481439543709 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13106 13106 (11 / 1000) ≤
    (0.008349710827 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13106) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.481439543709 : ℝ) ≤ √(13106 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13106)
  have hdiv : K / √(13106 : ℝ) ≤ K / 114.481439543709 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.481439543709 ≤ (0.008349710827 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13106.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13106 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13106 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13106 := gPlus_lower 13106
end BstLean.Part269.N13106

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13106
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035245365342 : ℝ) ≤ wn 13106 := by
  have hn : √(13106 : ℝ) ≤ 114.481439543710 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13106 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.481439543710 ≤ 2 / √(13106 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243945192 : ℝ) ≤ rhoBar 13106 BstLean.Part154.csC ∧
    rhoBar 13106 BstLean.Part154.csC ≤ 0.000243945569 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035245365342 : ℝ) / (1.295212 * 13106) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035245365343 : ℝ) / (1.29521 * 13106) := by gcongr
      _ ≤ (0.000243945569 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13106 BstLean.Part154.csC) ≤ 0.000975841786 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13106 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) ≤ 0.000186326998 ∧
    cc1 (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) ≤ 0.000118561162 ∧
    cc2 (rhoBar 13106 BstLean.Part154.csC) ≤ 0.000068825731 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13106 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13106 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13106 BstLean.Part154.csC * nuR (rhoBar 13106 BstLean.Part154.csC)) ≤ 0.000487906016 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243945569 : ℝ) * 0.000975841786 := by gcongr
      _ ≤ (0.000487906016 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13106 BstLean.Part154.csC) * nuR (rhoBar 13106 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975841786 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13106 BstLean.Part154.csC) * rhoBar 13106 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243945569 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243945569 / 2 + 0.399 * 0.000975841786 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186326998 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487906016 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118561162 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243945569 / 1.414213562 := by gcongr
      _ ≤ (0.000068825731 : ℝ) := by norm_num

end BstLean.Part269.N13106

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13106
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) ≤ 1.49930E-7 := by
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13106 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13106 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13106 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186326998 : ℝ) ^ 2 + 0.000118561162 ^ 2 + 3 * 0.000068825731 ^ 2 +
        2 * 0.797885 * 0.000186326998 * 0.000118561162 + 2 * 0.000186326998 * 0.000068825731 +
        4 * 0.797885 * 0.000118561162 * 0.000068825731 := by gcongr
    _ ≤ (1.49930E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13106 BstLean.Part154.csC Θ ≤ 0.002545069020 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13106 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13106 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13106 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035245365343 * 1.49930E-7 / (0.000243945192 : ℝ) := by gcongr
    _ ≤ 0.002545069020 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13106 BstLean.Part154.csC Θ ≤ 0.002822344422 + 0.000643096926 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13106 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13106 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035245365343 : ℝ) * ((2 * Θ * 0.000243945569 +
        (6863 / 10000) * 0.000243945569 * 13106 * 0.000975841786) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002822344422 + 0.000643096926 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13106 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13106 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13106 0.011 Θ ∧ gammaRatio 13106 0.011 Θ ≤ 0.000083862179 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13106 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035245365343 : ℝ) * 0.525 / ((1 - 0.011) * 13106) := by gcongr
      _ ≤ (0.000083862179 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13106 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13106 0.011 Θ) :=
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
    badAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13106 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13106 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13106 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13106 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13106 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13106 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13106 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13106 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13106 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13106 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035245365343 : ℝ) * 13106 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003171250004 + 0.003188165946 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13106

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13106
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13106 BstLean.Part154.csC) (piBar (rhoBar 13106 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13106 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13106 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13106 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13106 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13106 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13106 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13106 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13106 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13106 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13106 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051656237680 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13106) ≤ 0.010431713524 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13106 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035245365343)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010431713524 + 2 * 0.737676 / 13106) := by gcongr
    _ ≤ (0.051656237680 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13106 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13106

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13106
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521360041 : ℝ) ≤ plow 13106 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13106) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351637126)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336161236) : eMP 13106 0.011 xi bn ≤ 0.001150842951 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13106 : ℝ) * (1 - 0.011))) ≤ 0.000569077175 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336161236 / (13106 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569077175 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569077175 : ℝ) + 3.141593 * 0.052351637126 / (13106 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150842951 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351637126)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336161236) : PiBarMP 13106 12 0.011 xi bn ≤ 0.158709070236 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13106 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036553539309 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.850050505039 : ℝ) ≤ √((13106 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.481439543709 : ℝ) ≤ √(13106 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13106) ≤ 0.121700149110 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036553539309 + 0.052351637126 * 1.772454 / (2 * (113.850050505039 : ℝ))) * (1 + 0.001150842951) +
        8 / (13106 * 114.481439543709) + 0.121700149110 := by gcongr
    _ ≤ (0.158709070236 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351637126)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336161236) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280461039042) :
    parallelOracle 13106 0.011 xi bn cd ≤ 0.159668798020 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13106 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13106 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521360041 : ℝ) ≤ plow 13106 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.481439543709 : ℝ) ≤ √(13106 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280461039042 : ℝ) / (2 * 0.560521360041 * 114.481439543709)) * 0.158709070236 +
        0.280461039042 ^ 2 / (2 * 0.560521360041 * 114.481439543709) := by gcongr
    _ ≤ (0.159668798020 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351637126) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336161236)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280461039042) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13106 13106 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521360041 : ℝ) ≤ plow 13106 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.481439543709 : ℝ) ≤ √(13106 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13106 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13106 Θ 1.22 ≤ 0.011583541449 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.481439543709 := by gcongr <;> linarith
      _ ≤ (0.011583541449 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13106 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13106 13106 0.011 ≤ 0.008349710827 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13106 13106 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13106 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13106 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13106 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13106 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159668798020 + 0.011583541449 + (0.008349710827 : ℝ) *
        (1 + 2 * (0.280461039042 + 0.011583541449) / (0.560521360041 * 114.481439543709))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13106]

end BstLean.Part269.N13106

/-! The original eight local profiles supply actual 13106 moment certificates. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13106 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052351637126 ∧
    0 ≤ bN 13106 BstLean.Part154.csC (groupTheta g) ∧ bN 13106 BstLean.Part154.csC (groupTheta g) ≤ 0.001336161236 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13106 13106 0.011
      (momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13106 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13106 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13106 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228804801362 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13106 0.011
      (momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13106 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13106
/-! The actual computed-centre upper energy formula at 13106. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13106

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13106)
open BstLean.Part268 (cell13106)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084386935290
  | 2 => 0.085312098315
  | 3 => 0.086232949796
  | 4 => 0.087150331270
  | 5 => 0.088065277124
  | 6 => 0.088979045253
  | 7 => 0.089893150995
  | 8 => 0.090809404443
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13106 13106 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13106 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13106

/-! Actual upper energy certificates on all 43 source endpoints at 13106. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13106)
open BstLean.Part268 (cell13106)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13106 (gMinus 13106) (1 - (cell13106 i).lower) ≤ 1 ∧
    energyUpper 13106 (gMinus 13106) (BstLean.Part211.gPlus 13106)
      (finiteEnergy 13106 13106 0.011) (1 - (cell13106 i).lower) ≤
      (cell13106 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨10,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨11,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨12,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨13,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨14,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨15,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨16,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨17,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨18,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨19,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨20,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨21,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨22,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨23,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨24,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨25,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨26,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨27,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨28,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨29,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨30,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨31,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨32,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨33,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨34,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨35,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨36,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨37,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨38,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨39,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨40,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨41,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨42,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨43,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨44,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨45,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨46,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨47,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨48,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨49,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨50,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨51,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13106) (by norm_num)
        (q := 1 - (cell13106 ⟨52,by decide⟩).lower)
        (by norm_num [cell13106]) (by norm_num [cell13106])
      exact ⟨E.1,E.2.trans (by norm_num [cell13106])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13106

/-! Source-cell containment and simple scalar guards at 13106. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13106)
open BstLean.Part268 (cell13106)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13106 ⟨10,by decide⟩).lower ∧ (cell13106 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13106 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13106 ⟨11,by decide⟩).lower ∧ (cell13106 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13106 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13106 ⟨12,by decide⟩).lower ∧ (cell13106 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13106 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13106 ⟨13,by decide⟩).lower ∧ (cell13106 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13106 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13106 ⟨14,by decide⟩).lower ∧ (cell13106 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13106 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13106 ⟨15,by decide⟩).lower ∧ (cell13106 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13106 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13106 ⟨16,by decide⟩).lower ∧ (cell13106 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13106 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13106 ⟨17,by decide⟩).lower ∧ (cell13106 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13106 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13106 ⟨18,by decide⟩).lower ∧ (cell13106 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13106 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13106 ⟨19,by decide⟩).lower ∧ (cell13106 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13106 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13106 ⟨20,by decide⟩).lower ∧ (cell13106 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13106 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13106 ⟨21,by decide⟩).lower ∧ (cell13106 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13106 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13106 ⟨22,by decide⟩).lower ∧ (cell13106 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13106 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13106 ⟨23,by decide⟩).lower ∧ (cell13106 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13106 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13106 ⟨24,by decide⟩).lower ∧ (cell13106 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13106 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13106 ⟨25,by decide⟩).lower ∧ (cell13106 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13106 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13106 ⟨26,by decide⟩).lower ∧ (cell13106 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13106 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13106 ⟨27,by decide⟩).lower ∧ (cell13106 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13106 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13106 ⟨28,by decide⟩).lower ∧ (cell13106 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13106 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13106 ⟨29,by decide⟩).lower ∧ (cell13106 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13106 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13106 ⟨30,by decide⟩).lower ∧ (cell13106 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13106 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13106 ⟨31,by decide⟩).lower ∧ (cell13106 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13106 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13106 ⟨32,by decide⟩).lower ∧ (cell13106 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13106 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13106 ⟨33,by decide⟩).lower ∧ (cell13106 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13106 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13106 ⟨34,by decide⟩).lower ∧ (cell13106 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13106 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13106 ⟨35,by decide⟩).lower ∧ (cell13106 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13106 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13106 ⟨36,by decide⟩).lower ∧ (cell13106 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13106 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13106 ⟨37,by decide⟩).lower ∧ (cell13106 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13106 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13106 ⟨38,by decide⟩).lower ∧ (cell13106 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13106 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13106 ⟨39,by decide⟩).lower ∧ (cell13106 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13106 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13106 ⟨40,by decide⟩).lower ∧ (cell13106 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13106 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13106 ⟨41,by decide⟩).lower ∧ (cell13106 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13106 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13106 ⟨42,by decide⟩).lower ∧ (cell13106 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13106 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13106 ⟨43,by decide⟩).lower ∧ (cell13106 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13106 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13106 ⟨44,by decide⟩).lower ∧ (cell13106 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13106 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13106 ⟨45,by decide⟩).lower ∧ (cell13106 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13106 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13106 ⟨46,by decide⟩).lower ∧ (cell13106 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13106 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13106 ⟨47,by decide⟩).lower ∧ (cell13106 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13106 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13106 ⟨48,by decide⟩).lower ∧ (cell13106 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13106 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13106 ⟨49,by decide⟩).lower ∧ (cell13106 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13106 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13106 ⟨50,by decide⟩).lower ∧ (cell13106 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13106 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13106 ⟨51,by decide⟩).lower ∧ (cell13106 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13106 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13106 ⟨52,by decide⟩).lower ∧ (cell13106 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13106 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13106 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13106 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13106,cell13106,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13106 i).lower ∧
    (cell13106 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13106 i).upper ≤ (0.532 : ℝ) ∧
    (cell13106 i).centre ≤ (0.1 : ℝ) ∧ (cell13106 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13106 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13106 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13106

/-! The local source numeric instances at 13106 have no network premises. -/
namespace BstLean.Part269.N13106
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13106)
open BstLean.Part268 (cell13106)

noncomputable def sourceNumerics13106 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13106 (cell13106 i)
      scalarRow13106.M scalarRow13106.H scalarRow13106.xi := by
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
    energy_allowance := scalarRow13106.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13106]
    centre_nonneg := (scalarRow13106.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13106])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13106
/-! Actual 13107 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13107 ≤ (1.035244009150 : ℝ) := by
  have hr : (114.485806980603 : ℝ) ≤ √(13107 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.485806980603 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13107 13107 (11 / 1000) ≤
    (0.008349392298 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13107) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.485806980603 : ℝ) ≤ √(13107 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13107)
  have hdiv : K / √(13107 : ℝ) ≤ K / 114.485806980603 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.485806980603 ≤ (0.008349392298 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13107.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13107 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13107 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13107 := gPlus_lower 13107
end BstLean.Part269.N13107

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13107
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035244009149 : ℝ) ≤ wn 13107 := by
  have hn : √(13107 : ℝ) ≤ 114.485806980604 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13107 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.485806980604 ≤ 2 / √(13107 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243926260 : ℝ) ≤ rhoBar 13107 BstLean.Part154.csC ∧
    rhoBar 13107 BstLean.Part154.csC ≤ 0.000243926638 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035244009149 : ℝ) / (1.295212 * 13107) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035244009150 : ℝ) / (1.29521 * 13107) := by gcongr
      _ ≤ (0.000243926638 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13107 BstLean.Part154.csC) ≤ 0.000975766053 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13107 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) ≤ 0.000186312538 ∧
    cc1 (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) ≤ 0.000118551961 ∧
    cc2 (rhoBar 13107 BstLean.Part154.csC) ≤ 0.000068820390 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13107 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13107 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13107 BstLean.Part154.csC * nuR (rhoBar 13107 BstLean.Part154.csC)) ≤ 0.000487868152 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243926638 : ℝ) * 0.000975766053 := by gcongr
      _ ≤ (0.000487868152 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13107 BstLean.Part154.csC) * nuR (rhoBar 13107 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975766053 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13107 BstLean.Part154.csC) * rhoBar 13107 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243926638 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243926638 / 2 + 0.399 * 0.000975766053 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186312538 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487868152 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118551961 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243926638 / 1.414213562 := by gcongr
      _ ≤ (0.000068820390 : ℝ) := by norm_num

end BstLean.Part269.N13107

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13107
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) ≤ 1.49906E-7 := by
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13107 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13107 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13107 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186312538 : ℝ) ^ 2 + 0.000118551961 ^ 2 + 3 * 0.000068820390 ^ 2 +
        2 * 0.797885 * 0.000186312538 * 0.000118551961 + 2 * 0.000186312538 * 0.000068820390 +
        4 * 0.797885 * 0.000118551961 * 0.000068820390 := by gcongr
    _ ≤ (1.49906E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13107 BstLean.Part154.csC Θ ≤ 0.002544855785 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13107 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13107 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13107 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035244009150 * 1.49906E-7 / (0.000243926260 : ℝ) := by gcongr
    _ ≤ 0.002544855785 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13107 BstLean.Part154.csC Θ ≤ 0.002822117997 + 0.000643046177 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13107 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13107 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035244009150 : ℝ) * ((2 * Θ * 0.000243926638 +
        (6863 / 10000) * 0.000243926638 * 13107 * 0.000975766053) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002822117997 + 0.000643046177 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13107 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13107 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13107 0.011 Θ ∧ gammaRatio 13107 0.011 Θ ≤ 0.000083855671 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13107 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035244009150 : ℝ) * 0.525 / ((1 - 0.011) * 13107) := by gcongr
      _ ≤ (0.000083855671 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13107 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13107 0.011 Θ) :=
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
    badAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13107 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13107 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13107 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13107 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13107 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13107 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13107 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13107 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13107 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13107 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035244009150 : ℝ) * 13107 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003171023579 + 0.003187901962 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13107

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13107
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13107 BstLean.Part154.csC) (piBar (rhoBar 13107 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13107 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13107 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13107 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13107 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13107 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13107 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13107 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13107 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13107 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13107 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051654246046 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13107) ≤ 0.010431315572 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13107 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035244009150)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010431315572 + 2 * 0.737676 / 13107) := by gcongr
    _ ≤ (0.051654246046 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13107 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13107

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13107
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521402502 : ℝ) ≤ plow 13107 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13107) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351272110)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336049288) : eMP 13107 0.011 xi bn ≤ 0.001150750799 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13107 : ℝ) * (1 - 0.011))) ≤ 0.000569031627 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336049288 / (13107 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569031627 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569031627 : ℝ) + 3.141593 * 0.052351272110 / (13107 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150750799 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351272110)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336049288) : PiBarMP 13107 12 0.011 xi bn ≤ 0.158702872077 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13107 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036552007989 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.854393854607 : ℝ) ≤ √((13107 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.485806980603 : ℝ) ≤ √(13107 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13107) ≤ 0.121695506458 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036552007989 + 0.052351272110 * 1.772454 / (2 * (113.854393854607 : ℝ))) * (1 + 0.001150750799) +
        8 / (13107 * 114.485806980603) + 0.121695506458 := by gcongr
    _ ≤ (0.158702872077 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351272110)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336049288) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280458249748) :
    parallelOracle 13107 0.011 xi bn cd ≤ 0.159662533993 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13107 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13107 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521402502 : ℝ) ≤ plow 13107 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.485806980603 : ℝ) ≤ √(13107 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280458249748 : ℝ) / (2 * 0.560521402502 * 114.485806980603)) * 0.158702872077 +
        0.280458249748 ^ 2 / (2 * 0.560521402502 * 114.485806980603) := by gcongr
    _ ≤ (0.159662533993 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052351272110) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336049288)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280458249748) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13107 13107 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521402502 : ℝ) ≤ plow 13107 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.485806980603 : ℝ) ≤ √(13107 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13107 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13107 Θ 1.22 ≤ 0.011583099556 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.485806980603 := by gcongr <;> linarith
      _ ≤ (0.011583099556 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13107 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13107 13107 0.011 ≤ 0.008349392298 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13107 13107 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13107 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13107 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13107 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13107 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159662533993 + 0.011583099556 + (0.008349392298 : ℝ) *
        (1 + 2 * (0.280458249748 + 0.011583099556) / (0.560521402502 * 114.485806980603))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13107]

end BstLean.Part269.N13107

/-! The original eight local profiles supply actual 13107 moment certificates. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13107 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052351272110 ∧
    0 ≤ bN 13107 BstLean.Part154.csC (groupTheta g) ∧ bN 13107 BstLean.Part154.csC (groupTheta g) ≤ 0.001336049288 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13107 13107 0.011
      (momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13107 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13107 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13107 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228804003702 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13107 0.011
      (momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13107 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13107
/-! The actual computed-centre upper energy formula at 13107. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13107

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13107)
open BstLean.Part268 (cell13107)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084384398633
  | 2 => 0.085309529935
  | 3 => 0.086230345120
  | 4 => 0.087147684634
  | 5 => 0.088062581576
  | 6 => 0.088976292320
  | 7 => 0.089890330430
  | 8 => 0.090806503933
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13107 13107 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13107 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13107

/-! Actual upper energy certificates on all 43 source endpoints at 13107. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13107)
open BstLean.Part268 (cell13107)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13107 (gMinus 13107) (1 - (cell13107 i).lower) ≤ 1 ∧
    energyUpper 13107 (gMinus 13107) (BstLean.Part211.gPlus 13107)
      (finiteEnergy 13107 13107 0.011) (1 - (cell13107 i).lower) ≤
      (cell13107 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨10,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨11,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨12,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨13,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨14,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨15,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨16,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨17,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨18,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨19,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨20,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨21,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨22,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨23,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨24,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨25,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨26,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨27,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨28,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨29,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨30,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨31,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨32,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨33,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨34,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨35,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨36,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨37,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨38,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨39,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨40,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨41,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨42,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨43,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨44,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨45,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨46,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨47,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨48,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨49,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨50,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨51,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13107) (by norm_num)
        (q := 1 - (cell13107 ⟨52,by decide⟩).lower)
        (by norm_num [cell13107]) (by norm_num [cell13107])
      exact ⟨E.1,E.2.trans (by norm_num [cell13107])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13107

/-! Source-cell containment and simple scalar guards at 13107. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13107)
open BstLean.Part268 (cell13107)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13107 ⟨10,by decide⟩).lower ∧ (cell13107 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13107 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13107 ⟨11,by decide⟩).lower ∧ (cell13107 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13107 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13107 ⟨12,by decide⟩).lower ∧ (cell13107 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13107 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13107 ⟨13,by decide⟩).lower ∧ (cell13107 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13107 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13107 ⟨14,by decide⟩).lower ∧ (cell13107 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13107 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13107 ⟨15,by decide⟩).lower ∧ (cell13107 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13107 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13107 ⟨16,by decide⟩).lower ∧ (cell13107 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13107 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13107 ⟨17,by decide⟩).lower ∧ (cell13107 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13107 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13107 ⟨18,by decide⟩).lower ∧ (cell13107 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13107 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13107 ⟨19,by decide⟩).lower ∧ (cell13107 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13107 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13107 ⟨20,by decide⟩).lower ∧ (cell13107 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13107 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13107 ⟨21,by decide⟩).lower ∧ (cell13107 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13107 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13107 ⟨22,by decide⟩).lower ∧ (cell13107 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13107 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13107 ⟨23,by decide⟩).lower ∧ (cell13107 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13107 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13107 ⟨24,by decide⟩).lower ∧ (cell13107 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13107 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13107 ⟨25,by decide⟩).lower ∧ (cell13107 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13107 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13107 ⟨26,by decide⟩).lower ∧ (cell13107 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13107 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13107 ⟨27,by decide⟩).lower ∧ (cell13107 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13107 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13107 ⟨28,by decide⟩).lower ∧ (cell13107 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13107 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13107 ⟨29,by decide⟩).lower ∧ (cell13107 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13107 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13107 ⟨30,by decide⟩).lower ∧ (cell13107 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13107 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13107 ⟨31,by decide⟩).lower ∧ (cell13107 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13107 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13107 ⟨32,by decide⟩).lower ∧ (cell13107 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13107 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13107 ⟨33,by decide⟩).lower ∧ (cell13107 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13107 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13107 ⟨34,by decide⟩).lower ∧ (cell13107 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13107 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13107 ⟨35,by decide⟩).lower ∧ (cell13107 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13107 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13107 ⟨36,by decide⟩).lower ∧ (cell13107 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13107 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13107 ⟨37,by decide⟩).lower ∧ (cell13107 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13107 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13107 ⟨38,by decide⟩).lower ∧ (cell13107 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13107 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13107 ⟨39,by decide⟩).lower ∧ (cell13107 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13107 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13107 ⟨40,by decide⟩).lower ∧ (cell13107 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13107 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13107 ⟨41,by decide⟩).lower ∧ (cell13107 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13107 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13107 ⟨42,by decide⟩).lower ∧ (cell13107 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13107 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13107 ⟨43,by decide⟩).lower ∧ (cell13107 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13107 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13107 ⟨44,by decide⟩).lower ∧ (cell13107 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13107 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13107 ⟨45,by decide⟩).lower ∧ (cell13107 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13107 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13107 ⟨46,by decide⟩).lower ∧ (cell13107 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13107 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13107 ⟨47,by decide⟩).lower ∧ (cell13107 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13107 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13107 ⟨48,by decide⟩).lower ∧ (cell13107 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13107 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13107 ⟨49,by decide⟩).lower ∧ (cell13107 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13107 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13107 ⟨50,by decide⟩).lower ∧ (cell13107 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13107 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13107 ⟨51,by decide⟩).lower ∧ (cell13107 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13107 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13107 ⟨52,by decide⟩).lower ∧ (cell13107 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13107 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13107 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13107 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13107,cell13107,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13107 i).lower ∧
    (cell13107 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13107 i).upper ≤ (0.532 : ℝ) ∧
    (cell13107 i).centre ≤ (0.1 : ℝ) ∧ (cell13107 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13107 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13107 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13107

/-! The local source numeric instances at 13107 have no network premises. -/
namespace BstLean.Part269.N13107
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13107)
open BstLean.Part268 (cell13107)

noncomputable def sourceNumerics13107 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13107 (cell13107 i)
      scalarRow13107.M scalarRow13107.H scalarRow13107.xi := by
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
    energy_allowance := scalarRow13107.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13107]
    centre_nonneg := (scalarRow13107.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13107])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13107
/-! Actual 13108 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13108 ≤ (1.035242653113 : ℝ) := by
  have hr : (114.490174250893 : ℝ) ≤ √(13108 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.490174250893 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13108 13108 (11 / 1000) ≤
    (0.008349073805 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13108) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.490174250893 : ℝ) ≤ √(13108 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13108)
  have hdiv : K / √(13108 : ℝ) ≤ K / 114.490174250893 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.490174250893 ≤ (0.008349073805 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13108.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13108 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13108 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13108 := gPlus_lower 13108
end BstLean.Part269.N13108

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13108
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035242653112 : ℝ) ≤ wn 13108 := by
  have hn : √(13108 : ℝ) ≤ 114.490174250894 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13108 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.490174250894 ≤ 2 / √(13108 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243907332 : ℝ) ≤ rhoBar 13108 BstLean.Part154.csC ∧
    rhoBar 13108 BstLean.Part154.csC ≤ 0.000243907709 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035242653112 : ℝ) / (1.295212 * 13108) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035242653113 : ℝ) / (1.29521 * 13108) := by gcongr
      _ ≤ (0.000243907709 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13108 BstLean.Part154.csC) ≤ 0.000975690327 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13108 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) ≤ 0.000186298079 ∧
    cc1 (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) ≤ 0.000118542761 ∧
    cc2 (rhoBar 13108 BstLean.Part154.csC) ≤ 0.000068815050 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13108 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13108 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13108 BstLean.Part154.csC * nuR (rhoBar 13108 BstLean.Part154.csC)) ≤ 0.000487830291 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243907709 : ℝ) * 0.000975690327 := by gcongr
      _ ≤ (0.000487830291 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13108 BstLean.Part154.csC) * nuR (rhoBar 13108 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975690327 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13108 BstLean.Part154.csC) * rhoBar 13108 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243907709 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243907709 / 2 + 0.399 * 0.000975690327 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186298079 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487830291 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118542761 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243907709 / 1.414213562 := by gcongr
      _ ≤ (0.000068815050 : ℝ) := by norm_num

end BstLean.Part269.N13108

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13108
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) ≤ 1.49883E-7 := by
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13108 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13108 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13108 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186298079 : ℝ) ^ 2 + 0.000118542761 ^ 2 + 3 * 0.000068815050 ^ 2 +
        2 * 0.797885 * 0.000186298079 * 0.000118542761 + 2 * 0.000186298079 * 0.000068815050 +
        4 * 0.797885 * 0.000118542761 * 0.000068815050 := by gcongr
    _ ≤ (1.49883E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13108 BstLean.Part154.csC Θ ≤ 0.002544659455 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13108 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13108 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13108 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035242653113 * 1.49883E-7 / (0.000243907332 : ℝ) := by gcongr
    _ ≤ 0.002544659455 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13108 BstLean.Part154.csC Θ ≤ 0.002821891583 + 0.000642995434 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13108 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13108 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035242653113 : ℝ) * ((2 * Θ * 0.000243907709 +
        (6863 / 10000) * 0.000243907709 * 13108 * 0.000975690327) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002821891583 + 0.000642995434 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13108 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13108 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13108 0.011 Θ ∧ gammaRatio 13108 0.011 Θ ≤ 0.000083849164 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13108 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035242653113 : ℝ) * 0.525 / ((1 - 0.011) * 13108) := by gcongr
      _ ≤ (0.000083849164 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13108 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13108 0.011 Θ) :=
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
    badAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13108 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13108 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13108 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13108 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13108 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13108 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13108 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13108 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13108 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13108 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035242653113 : ℝ) * 13108 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003170797165 + 0.003187654889 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13108

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13108
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13108 BstLean.Part154.csC) (piBar (rhoBar 13108 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13108 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13108 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13108 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13108 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13108 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13108 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13108 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13108 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13108 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13108 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051652254638 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13108) ≤ 0.010430917665 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13108 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035242653113)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010430917665 + 2 * 0.737676 / 13108) := by gcongr
    _ ≤ (0.051652254638 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13108 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13108

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13108
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521444957 : ℝ) ≤ plow 13108 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13108) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350915982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335946214) : eMP 13108 0.011 xi bn ≤ 0.001150662432 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13108 : ℝ) * (1 - 0.011))) ≤ 0.000568987971 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335946214 / (13108 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568987971 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568987971 : ℝ) + 3.141593 * 0.052350915982 / (13108 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150662432 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350915982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335946214) : PiBarMP 13108 12 0.011 xi bn ≤ 0.158696796130 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13108 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036550597998 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.858737038489 : ℝ) ≤ √((13108 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.490174250893 : ℝ) ≤ √(13108 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13108) ≤ 0.121690864338 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036550597998 + 0.052350915982 * 1.772454 / (2 * (113.858737038489 : ℝ))) * (1 + 0.001150662432) +
        8 / (13108 * 114.490174250893) + 0.121690864338 := by gcongr
    _ ≤ (0.158696796130 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350915982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335946214) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280455480101) :
    parallelOracle 13108 0.011 xi bn cd ≤ 0.159656392561 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13108 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13108 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521444957 : ℝ) ≤ plow 13108 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.490174250893 : ℝ) ≤ √(13108 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280455480101 : ℝ) / (2 * 0.560521444957 * 114.490174250893)) * 0.158696796130 +
        0.280455480101 ^ 2 / (2 * 0.560521444957 * 114.490174250893) := by gcongr
    _ ≤ (0.159656392561 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350915982) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335946214)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280455480101) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13108 13108 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521444957 : ℝ) ≤ plow 13108 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.490174250893 : ℝ) ≤ √(13108 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13108 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13108 Θ 1.22 ≤ 0.011582657715 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.490174250893 := by gcongr <;> linarith
      _ ≤ (0.011582657715 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13108 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13108 13108 0.011 ≤ 0.008349073805 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13108 13108 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13108 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13108 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13108 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13108 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159656392561 + 0.011582657715 + (0.008349073805 : ℝ) *
        (1 + 2 * (0.280455480101 + 0.011582657715) / (0.560521444957 * 114.490174250893))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13108]

end BstLean.Part269.N13108

/-! The original eight local profiles supply actual 13108 moment certificates. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13108 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052350915982 ∧
    0 ≤ bN 13108 BstLean.Part154.csC (groupTheta g) ∧ bN 13108 BstLean.Part154.csC (groupTheta g) ≤ 0.001335946214 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13108 13108 0.011
      (momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13108 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13108 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13108 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228803225463 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13108 0.011
      (momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13108 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13108
/-! The actual computed-centre upper energy formula at 13108. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13108

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13108)
open BstLean.Part268 (cell13108)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084381862708
  | 2 => 0.085306962314
  | 3 => 0.086227741232
  | 4 => 0.087145038825
  | 5 => 0.088059886900
  | 6 => 0.088973540318
  | 7 => 0.089887510865
  | 8 => 0.090803604507
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13108 13108 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13108 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13108

/-! Actual upper energy certificates on all 43 source endpoints at 13108. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13108)
open BstLean.Part268 (cell13108)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13108 (gMinus 13108) (1 - (cell13108 i).lower) ≤ 1 ∧
    energyUpper 13108 (gMinus 13108) (BstLean.Part211.gPlus 13108)
      (finiteEnergy 13108 13108 0.011) (1 - (cell13108 i).lower) ≤
      (cell13108 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨10,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨11,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨12,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨13,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨14,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨15,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨16,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨17,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨18,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨19,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨20,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨21,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨22,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨23,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨24,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨25,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨26,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨27,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨28,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨29,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨30,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨31,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨32,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨33,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨34,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨35,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨36,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨37,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨38,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨39,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨40,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨41,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨42,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨43,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨44,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨45,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨46,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨47,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨48,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨49,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨50,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨51,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13108) (by norm_num)
        (q := 1 - (cell13108 ⟨52,by decide⟩).lower)
        (by norm_num [cell13108]) (by norm_num [cell13108])
      exact ⟨E.1,E.2.trans (by norm_num [cell13108])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13108

/-! Source-cell containment and simple scalar guards at 13108. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13108)
open BstLean.Part268 (cell13108)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13108 ⟨10,by decide⟩).lower ∧ (cell13108 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13108 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13108 ⟨11,by decide⟩).lower ∧ (cell13108 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13108 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13108 ⟨12,by decide⟩).lower ∧ (cell13108 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13108 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13108 ⟨13,by decide⟩).lower ∧ (cell13108 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13108 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13108 ⟨14,by decide⟩).lower ∧ (cell13108 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13108 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13108 ⟨15,by decide⟩).lower ∧ (cell13108 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13108 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13108 ⟨16,by decide⟩).lower ∧ (cell13108 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13108 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13108 ⟨17,by decide⟩).lower ∧ (cell13108 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13108 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13108 ⟨18,by decide⟩).lower ∧ (cell13108 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13108 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13108 ⟨19,by decide⟩).lower ∧ (cell13108 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13108 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13108 ⟨20,by decide⟩).lower ∧ (cell13108 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13108 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13108 ⟨21,by decide⟩).lower ∧ (cell13108 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13108 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13108 ⟨22,by decide⟩).lower ∧ (cell13108 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13108 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13108 ⟨23,by decide⟩).lower ∧ (cell13108 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13108 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13108 ⟨24,by decide⟩).lower ∧ (cell13108 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13108 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13108 ⟨25,by decide⟩).lower ∧ (cell13108 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13108 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13108 ⟨26,by decide⟩).lower ∧ (cell13108 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13108 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13108 ⟨27,by decide⟩).lower ∧ (cell13108 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13108 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13108 ⟨28,by decide⟩).lower ∧ (cell13108 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13108 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13108 ⟨29,by decide⟩).lower ∧ (cell13108 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13108 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13108 ⟨30,by decide⟩).lower ∧ (cell13108 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13108 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13108 ⟨31,by decide⟩).lower ∧ (cell13108 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13108 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13108 ⟨32,by decide⟩).lower ∧ (cell13108 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13108 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13108 ⟨33,by decide⟩).lower ∧ (cell13108 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13108 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13108 ⟨34,by decide⟩).lower ∧ (cell13108 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13108 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13108 ⟨35,by decide⟩).lower ∧ (cell13108 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13108 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13108 ⟨36,by decide⟩).lower ∧ (cell13108 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13108 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13108 ⟨37,by decide⟩).lower ∧ (cell13108 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13108 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13108 ⟨38,by decide⟩).lower ∧ (cell13108 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13108 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13108 ⟨39,by decide⟩).lower ∧ (cell13108 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13108 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13108 ⟨40,by decide⟩).lower ∧ (cell13108 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13108 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13108 ⟨41,by decide⟩).lower ∧ (cell13108 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13108 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13108 ⟨42,by decide⟩).lower ∧ (cell13108 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13108 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13108 ⟨43,by decide⟩).lower ∧ (cell13108 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13108 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13108 ⟨44,by decide⟩).lower ∧ (cell13108 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13108 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13108 ⟨45,by decide⟩).lower ∧ (cell13108 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13108 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13108 ⟨46,by decide⟩).lower ∧ (cell13108 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13108 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13108 ⟨47,by decide⟩).lower ∧ (cell13108 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13108 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13108 ⟨48,by decide⟩).lower ∧ (cell13108 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13108 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13108 ⟨49,by decide⟩).lower ∧ (cell13108 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13108 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13108 ⟨50,by decide⟩).lower ∧ (cell13108 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13108 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13108 ⟨51,by decide⟩).lower ∧ (cell13108 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13108 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13108 ⟨52,by decide⟩).lower ∧ (cell13108 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13108 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13108 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13108 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13108,cell13108,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13108 i).lower ∧
    (cell13108 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13108 i).upper ≤ (0.532 : ℝ) ∧
    (cell13108 i).centre ≤ (0.1 : ℝ) ∧ (cell13108 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13108 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13108 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13108

/-! The local source numeric instances at 13108 have no network premises. -/
namespace BstLean.Part269.N13108
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13108)
open BstLean.Part268 (cell13108)

noncomputable def sourceNumerics13108 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13108 (cell13108 i)
      scalarRow13108.M scalarRow13108.H scalarRow13108.xi := by
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
    energy_allowance := scalarRow13108.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13108]
    centre_nonneg := (scalarRow13108.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13108])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13108
/-! Actual 13109 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13109 ≤ (1.035241297233 : ℝ) := by
  have hr : (114.494541354599 : ℝ) ≤ √(13109 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.494541354599 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13109 13109 (11 / 1000) ≤
    (0.008348755348 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13109) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.494541354599 : ℝ) ≤ √(13109 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13109)
  have hdiv : K / √(13109 : ℝ) ≤ K / 114.494541354599 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.494541354599 ≤ (0.008348755348 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13109.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13109 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13109 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13109 := gPlus_lower 13109
end BstLean.Part269.N13109

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13109
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035241297232 : ℝ) ≤ wn 13109 := by
  have hn : √(13109 : ℝ) ≤ 114.494541354600 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13109 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.494541354600 ≤ 2 / √(13109 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243888406 : ℝ) ≤ rhoBar 13109 BstLean.Part154.csC ∧
    rhoBar 13109 BstLean.Part154.csC ≤ 0.000243888784 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035241297232 : ℝ) / (1.295212 * 13109) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035241297233 : ℝ) / (1.29521 * 13109) := by gcongr
      _ ≤ (0.000243888784 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13109 BstLean.Part154.csC) ≤ 0.000975614618 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13109 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) ≤ 0.000186283624 ∧
    cc1 (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) ≤ 0.000118533563 ∧
    cc2 (rhoBar 13109 BstLean.Part154.csC) ≤ 0.000068809710 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13109 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13109 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13109 BstLean.Part154.csC * nuR (rhoBar 13109 BstLean.Part154.csC)) ≤ 0.000487792439 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243888784 : ℝ) * 0.000975614618 := by gcongr
      _ ≤ (0.000487792439 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13109 BstLean.Part154.csC) * nuR (rhoBar 13109 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975614618 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13109 BstLean.Part154.csC) * rhoBar 13109 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243888784 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243888784 / 2 + 0.399 * 0.000975614618 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186283624 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487792439 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118533563 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243888784 / 1.414213562 := by gcongr
      _ ≤ (0.000068809710 : ℝ) := by norm_num

end BstLean.Part269.N13109

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13109
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) ≤ 1.49860E-7 := by
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13109 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13109 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13109 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186283624 : ℝ) ^ 2 + 0.000118533563 ^ 2 + 3 * 0.000068809710 ^ 2 +
        2 * 0.797885 * 0.000186283624 * 0.000118533563 + 2 * 0.000186283624 * 0.000068809710 +
        4 * 0.797885 * 0.000118533563 * 0.000068809710 := by gcongr
    _ ≤ (1.49860E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13109 BstLean.Part154.csC Θ ≤ 0.002544463074 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13109 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13109 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13109 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035241297233 * 1.49860E-7 / (0.000243888406 : ℝ) := by gcongr
    _ ≤ 0.002544463074 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13109 BstLean.Part154.csC Θ ≤ 0.002821665232 + 0.000642944701 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13109 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13109 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035241297233 : ℝ) * ((2 * Θ * 0.000243888784 +
        (6863 / 10000) * 0.000243888784 * 13109 * 0.000975614618) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002821665232 + 0.000642944701 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13109 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13109 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13109 0.011 Θ ∧ gammaRatio 13109 0.011 Θ ≤ 0.000083842657 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13109 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035241297233 : ℝ) * 0.525 / ((1 - 0.011) * 13109) := by gcongr
      _ ≤ (0.000083842657 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13109 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13109 0.011 Θ) :=
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
    badAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13109 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13109 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13109 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13109 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13109 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13109 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13109 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13109 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13109 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13109 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035241297233 : ℝ) * 13109 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003170570814 + 0.003187407775 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13109

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13109
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13109 BstLean.Part154.csC) (piBar (rhoBar 13109 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13109 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13109 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13109 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13109 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13109 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13109 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13109 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13109 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13109 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13109 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051650263468 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13109) ≤ 0.010430519805 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13109 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035241297233)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010430519805 + 2 * 0.737676 / 13109) := by gcongr
    _ ≤ (0.051650263468 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13109 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13109

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13109
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521487405 : ℝ) ≤ plow 13109 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13109) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350559896)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335843114) : eMP 13109 0.011 xi bn ≤ 0.001150574064 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13109 : ℝ) * (1 - 0.011))) ≤ 0.000568944314 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335843114 / (13109 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568944314 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568944314 : ℝ) + 3.141593 * 0.052350559896 / (13109 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150574064 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350559896)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335843114) : PiBarMP 13109 12 0.011 xi bn ≤ 0.158690720307 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13109 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036549187597 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.863080056706 : ℝ) ≤ √((13109 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.494541354599 : ℝ) ≤ √(13109 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13109) ≤ 0.121686222749 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036549187597 + 0.052350559896 * 1.772454 / (2 * (113.863080056706 : ℝ))) * (1 + 0.001150574064) +
        8 / (13109 * 114.494541354599) + 0.121686222749 := by gcongr
    _ ≤ (0.158690720307 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350559896)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335843114) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280452710781) :
    parallelOracle 13109 0.011 xi bn cd ≤ 0.159650251262 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13109 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13109 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521487405 : ℝ) ≤ plow 13109 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.494541354599 : ℝ) ≤ √(13109 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280452710781 : ℝ) / (2 * 0.560521487405 * 114.494541354599)) * 0.158690720307 +
        0.280452710781 ^ 2 / (2 * 0.560521487405 * 114.494541354599) := by gcongr
    _ ≤ (0.159650251262 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350559896) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335843114)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280452710781) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13109 13109 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521487405 : ℝ) ≤ plow 13109 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.494541354599 : ℝ) ≤ √(13109 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13109 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13109 Θ 1.22 ≤ 0.011582215924 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.494541354599 := by gcongr <;> linarith
      _ ≤ (0.011582215924 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13109 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13109 13109 0.011 ≤ 0.008348755348 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13109 13109 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13109 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13109 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13109 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13109 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159650251262 + 0.011582215924 + (0.008348755348 : ℝ) *
        (1 + 2 * (0.280452710781 + 0.011582215924) / (0.560521487405 * 114.494541354599))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13109]

end BstLean.Part269.N13109

/-! The original eight local profiles supply actual 13109 moment certificates. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13109 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052350559896 ∧
    0 ≤ bN 13109 BstLean.Part154.csC (groupTheta g) ∧ bN 13109 BstLean.Part154.csC (groupTheta g) ≤ 0.001335843114 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13109 13109 0.011
      (momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13109 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13109 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13109 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228802447313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13109 0.011
      (momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13109 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13109
/-! The actual computed-centre upper energy formula at 13109. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13109

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13109)
open BstLean.Part268 (cell13109)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084379327516
  | 2 => 0.085304395449
  | 3 => 0.086225138132
  | 4 => 0.087142393841
  | 5 => 0.088057193098
  | 6 => 0.088970789246
  | 7 => 0.089884692300
  | 8 => 0.090800706165
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13109 13109 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13109 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13109

/-! Actual upper energy certificates on all 43 source endpoints at 13109. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13109)
open BstLean.Part268 (cell13109)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13109 (gMinus 13109) (1 - (cell13109 i).lower) ≤ 1 ∧
    energyUpper 13109 (gMinus 13109) (BstLean.Part211.gPlus 13109)
      (finiteEnergy 13109 13109 0.011) (1 - (cell13109 i).lower) ≤
      (cell13109 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨10,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨11,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨12,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨13,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨14,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨15,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨16,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨17,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨18,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨19,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨20,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨21,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨22,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨23,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨24,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨25,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨26,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨27,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨28,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨29,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨30,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨31,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨32,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨33,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨34,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨35,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨36,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨37,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨38,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨39,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨40,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨41,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨42,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨43,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨44,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨45,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨46,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨47,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨48,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨49,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨50,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨51,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13109) (by norm_num)
        (q := 1 - (cell13109 ⟨52,by decide⟩).lower)
        (by norm_num [cell13109]) (by norm_num [cell13109])
      exact ⟨E.1,E.2.trans (by norm_num [cell13109])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13109

/-! Source-cell containment and simple scalar guards at 13109. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13109)
open BstLean.Part268 (cell13109)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13109 ⟨10,by decide⟩).lower ∧ (cell13109 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13109 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13109 ⟨11,by decide⟩).lower ∧ (cell13109 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13109 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13109 ⟨12,by decide⟩).lower ∧ (cell13109 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13109 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13109 ⟨13,by decide⟩).lower ∧ (cell13109 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13109 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13109 ⟨14,by decide⟩).lower ∧ (cell13109 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13109 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13109 ⟨15,by decide⟩).lower ∧ (cell13109 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13109 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13109 ⟨16,by decide⟩).lower ∧ (cell13109 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13109 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13109 ⟨17,by decide⟩).lower ∧ (cell13109 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13109 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13109 ⟨18,by decide⟩).lower ∧ (cell13109 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13109 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13109 ⟨19,by decide⟩).lower ∧ (cell13109 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13109 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13109 ⟨20,by decide⟩).lower ∧ (cell13109 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13109 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13109 ⟨21,by decide⟩).lower ∧ (cell13109 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13109 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13109 ⟨22,by decide⟩).lower ∧ (cell13109 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13109 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13109 ⟨23,by decide⟩).lower ∧ (cell13109 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13109 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13109 ⟨24,by decide⟩).lower ∧ (cell13109 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13109 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13109 ⟨25,by decide⟩).lower ∧ (cell13109 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13109 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13109 ⟨26,by decide⟩).lower ∧ (cell13109 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13109 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13109 ⟨27,by decide⟩).lower ∧ (cell13109 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13109 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13109 ⟨28,by decide⟩).lower ∧ (cell13109 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13109 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13109 ⟨29,by decide⟩).lower ∧ (cell13109 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13109 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13109 ⟨30,by decide⟩).lower ∧ (cell13109 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13109 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13109 ⟨31,by decide⟩).lower ∧ (cell13109 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13109 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13109 ⟨32,by decide⟩).lower ∧ (cell13109 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13109 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13109 ⟨33,by decide⟩).lower ∧ (cell13109 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13109 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13109 ⟨34,by decide⟩).lower ∧ (cell13109 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13109 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13109 ⟨35,by decide⟩).lower ∧ (cell13109 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13109 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13109 ⟨36,by decide⟩).lower ∧ (cell13109 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13109 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13109 ⟨37,by decide⟩).lower ∧ (cell13109 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13109 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13109 ⟨38,by decide⟩).lower ∧ (cell13109 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13109 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13109 ⟨39,by decide⟩).lower ∧ (cell13109 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13109 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13109 ⟨40,by decide⟩).lower ∧ (cell13109 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13109 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13109 ⟨41,by decide⟩).lower ∧ (cell13109 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13109 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13109 ⟨42,by decide⟩).lower ∧ (cell13109 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13109 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13109 ⟨43,by decide⟩).lower ∧ (cell13109 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13109 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13109 ⟨44,by decide⟩).lower ∧ (cell13109 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13109 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13109 ⟨45,by decide⟩).lower ∧ (cell13109 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13109 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13109 ⟨46,by decide⟩).lower ∧ (cell13109 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13109 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13109 ⟨47,by decide⟩).lower ∧ (cell13109 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13109 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13109 ⟨48,by decide⟩).lower ∧ (cell13109 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13109 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13109 ⟨49,by decide⟩).lower ∧ (cell13109 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13109 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13109 ⟨50,by decide⟩).lower ∧ (cell13109 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13109 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13109 ⟨51,by decide⟩).lower ∧ (cell13109 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13109 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13109 ⟨52,by decide⟩).lower ∧ (cell13109 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13109 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13109 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13109 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13109,cell13109,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13109 i).lower ∧
    (cell13109 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13109 i).upper ≤ (0.532 : ℝ) ∧
    (cell13109 i).centre ≤ (0.1 : ℝ) ∧ (cell13109 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13109 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13109 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13109

/-! The local source numeric instances at 13109 have no network premises. -/
namespace BstLean.Part269.N13109
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13109)
open BstLean.Part268 (cell13109)

noncomputable def sourceNumerics13109 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13109 (cell13109 i)
      scalarRow13109.M scalarRow13109.H scalarRow13109.xi := by
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
    energy_allowance := scalarRow13109.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13109]
    centre_nonneg := (scalarRow13109.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13109])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13109
/-! Actual 13110 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13110 ≤ (1.035239941508 : ℝ) := by
  have hr : (114.498908291738 : ℝ) ≤ √(13110 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.498908291738 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13110 13110 (11 / 1000) ≤
    (0.008348436928 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13110) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.498908291738 : ℝ) ≤ √(13110 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13110)
  have hdiv : K / √(13110 : ℝ) ≤ K / 114.498908291738 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.498908291738 ≤ (0.008348436928 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13110.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13110 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13110 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13110 := gPlus_lower 13110
end BstLean.Part269.N13110

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13110
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035239941507 : ℝ) ≤ wn 13110 := by
  have hn : √(13110 : ℝ) ≤ 114.498908291739 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13110 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.498908291739 ≤ 2 / √(13110 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243869484 : ℝ) ≤ rhoBar 13110 BstLean.Part154.csC ∧
    rhoBar 13110 BstLean.Part154.csC ≤ 0.000243869861 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035239941507 : ℝ) / (1.295212 * 13110) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035239941508 : ℝ) / (1.29521 * 13110) := by gcongr
      _ ≤ (0.000243869861 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13110 BstLean.Part154.csC) ≤ 0.000975538917 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13110 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) ≤ 0.000186269169 ∧
    cc1 (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) ≤ 0.000118524366 ∧
    cc2 (rhoBar 13110 BstLean.Part154.csC) ≤ 0.000068804371 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13110 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13110 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13110 BstLean.Part154.csC * nuR (rhoBar 13110 BstLean.Part154.csC)) ≤ 0.000487754591 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243869861 : ℝ) * 0.000975538917 := by gcongr
      _ ≤ (0.000487754591 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13110 BstLean.Part154.csC) * nuR (rhoBar 13110 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975538917 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13110 BstLean.Part154.csC) * rhoBar 13110 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243869861 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243869861 / 2 + 0.399 * 0.000975538917 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186269169 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487754591 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118524366 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243869861 / 1.414213562 := by gcongr
      _ ≤ (0.000068804371 : ℝ) := by norm_num

end BstLean.Part269.N13110

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13110
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) ≤ 1.49837E-7 := by
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13110 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13110 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13110 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186269169 : ℝ) ^ 2 + 0.000118524366 ^ 2 + 3 * 0.000068804371 ^ 2 +
        2 * 0.797885 * 0.000186269169 * 0.000118524366 + 2 * 0.000186269169 * 0.000068804371 +
        4 * 0.797885 * 0.000118524366 * 0.000068804371 := by gcongr
    _ ≤ (1.49837E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13110 BstLean.Part154.csC Θ ≤ 0.002544266623 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13110 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13110 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13110 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035239941508 * 1.49837E-7 / (0.000243869484 : ℝ) := by gcongr
    _ ≤ 0.002544266623 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13110 BstLean.Part154.csC Θ ≤ 0.002821438896 + 0.000642893974 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13110 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13110 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035239941508 : ℝ) * ((2 * Θ * 0.000243869861 +
        (6863 / 10000) * 0.000243869861 * 13110 * 0.000975538917) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002821438896 + 0.000642893974 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13110 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13110 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13110 0.011 Θ ∧ gammaRatio 13110 0.011 Θ ≤ 0.000083836152 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13110 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035239941508 : ℝ) * 0.525 / ((1 - 0.011) * 13110) := by gcongr
      _ ≤ (0.000083836152 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13110 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13110 0.011 Θ) :=
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
    badAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13110 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13110 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13110 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13110 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13110 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13110 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13110 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13110 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13110 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13110 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035239941508 : ℝ) * 13110 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003170344478 + 0.003187160597 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13110

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13110
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13110 BstLean.Part154.csC) (piBar (rhoBar 13110 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13110 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13110 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13110 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13110 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13110 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13110 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13110 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13110 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13110 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13110 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051648272519 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13110) ≤ 0.010430121989 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13110 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035239941508)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010430121989 + 2 * 0.737676 / 13110) := by gcongr
    _ ≤ (0.051648272519 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13110 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13110

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13110
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521529847 : ℝ) ≤ plow 13110 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13110) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350203792)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335739978) : eMP 13110 0.011 xi bn ≤ 0.001150485687 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13110 : ℝ) * (1 - 0.011))) ≤ 0.000568900652 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335739978 / (13110 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568900652 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568900652 : ℝ) + 3.141593 * 0.052350203792 / (13110 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150485687 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350203792)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335739978) : PiBarMP 13110 12 0.011 xi bn ≤ 0.158684644470 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13110 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036547776650 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.867422909276 : ℝ) ≤ √((13110 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.498908291738 : ℝ) ≤ √(13110 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13110) ≤ 0.121681581691 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036547776650 + 0.052350203792 * 1.772454 / (2 * (113.867422909276 : ℝ))) * (1 + 0.001150485687) +
        8 / (13110 * 114.498908291738) + 0.121681581691 := by gcongr
    _ ≤ (0.158684644470 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350203792)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335739978) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280449941639) :
    parallelOracle 13110 0.011 xi bn cd ≤ 0.159644109957 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13110 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13110 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521529847 : ℝ) ≤ plow 13110 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.498908291738 : ℝ) ≤ √(13110 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280449941639 : ℝ) / (2 * 0.560521529847 * 114.498908291738)) * 0.158684644470 +
        0.280449941639 ^ 2 / (2 * 0.560521529847 * 114.498908291738) := by gcongr
    _ ≤ (0.159644109957 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052350203792) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335739978)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280449941639) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13110 13110 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521529847 : ℝ) ≤ plow 13110 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.498908291738 : ℝ) ≤ √(13110 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13110 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13110 Θ 1.22 ≤ 0.011581774183 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.498908291738 := by gcongr <;> linarith
      _ ≤ (0.011581774183 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13110 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13110 13110 0.011 ≤ 0.008348436928 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13110 13110 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13110 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13110 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13110 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13110 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159644109957 + 0.011581774183 + (0.008348436928 : ℝ) *
        (1 + 2 * (0.280449941639 + 0.011581774183) / (0.560521529847 * 114.498908291738))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13110]

end BstLean.Part269.N13110

/-! The original eight local profiles supply actual 13110 moment certificates. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13110 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052350203792 ∧
    0 ≤ bN 13110 BstLean.Part154.csC (groupTheta g) ∧ bN 13110 BstLean.Part154.csC (groupTheta g) ≤ 0.001335739978 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13110 13110 0.011
      (momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13110 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13110 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13110 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228801669120 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13110 0.011
      (momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13110 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13110
/-! The actual computed-centre upper energy formula at 13110. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13110

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13110)
open BstLean.Part268 (cell13110)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084376793056
  | 2 => 0.085301829341
  | 3 => 0.086222535820
  | 4 => 0.087139749683
  | 5 => 0.088054500168
  | 6 => 0.088968039103
  | 7 => 0.089881874734
  | 8 => 0.090797808906
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13110 13110 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13110 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13110

/-! Actual upper energy certificates on all 43 source endpoints at 13110. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13110)
open BstLean.Part268 (cell13110)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13110 (gMinus 13110) (1 - (cell13110 i).lower) ≤ 1 ∧
    energyUpper 13110 (gMinus 13110) (BstLean.Part211.gPlus 13110)
      (finiteEnergy 13110 13110 0.011) (1 - (cell13110 i).lower) ≤
      (cell13110 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨10,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨11,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨12,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨13,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨14,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨15,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨16,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨17,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨18,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨19,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨20,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨21,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨22,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨23,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨24,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨25,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨26,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨27,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨28,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨29,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨30,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨31,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨32,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨33,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨34,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨35,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨36,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨37,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨38,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨39,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨40,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨41,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨42,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨43,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨44,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨45,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨46,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨47,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨48,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨49,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨50,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨51,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13110) (by norm_num)
        (q := 1 - (cell13110 ⟨52,by decide⟩).lower)
        (by norm_num [cell13110]) (by norm_num [cell13110])
      exact ⟨E.1,E.2.trans (by norm_num [cell13110])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13110

/-! Source-cell containment and simple scalar guards at 13110. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13110)
open BstLean.Part268 (cell13110)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13110 ⟨10,by decide⟩).lower ∧ (cell13110 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13110 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13110 ⟨11,by decide⟩).lower ∧ (cell13110 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13110 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13110 ⟨12,by decide⟩).lower ∧ (cell13110 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13110 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13110 ⟨13,by decide⟩).lower ∧ (cell13110 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13110 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13110 ⟨14,by decide⟩).lower ∧ (cell13110 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13110 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13110 ⟨15,by decide⟩).lower ∧ (cell13110 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13110 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13110 ⟨16,by decide⟩).lower ∧ (cell13110 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13110 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13110 ⟨17,by decide⟩).lower ∧ (cell13110 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13110 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13110 ⟨18,by decide⟩).lower ∧ (cell13110 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13110 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13110 ⟨19,by decide⟩).lower ∧ (cell13110 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13110 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13110 ⟨20,by decide⟩).lower ∧ (cell13110 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13110 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13110 ⟨21,by decide⟩).lower ∧ (cell13110 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13110 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13110 ⟨22,by decide⟩).lower ∧ (cell13110 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13110 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13110 ⟨23,by decide⟩).lower ∧ (cell13110 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13110 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13110 ⟨24,by decide⟩).lower ∧ (cell13110 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13110 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13110 ⟨25,by decide⟩).lower ∧ (cell13110 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13110 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13110 ⟨26,by decide⟩).lower ∧ (cell13110 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13110 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13110 ⟨27,by decide⟩).lower ∧ (cell13110 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13110 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13110 ⟨28,by decide⟩).lower ∧ (cell13110 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13110 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13110 ⟨29,by decide⟩).lower ∧ (cell13110 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13110 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13110 ⟨30,by decide⟩).lower ∧ (cell13110 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13110 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13110 ⟨31,by decide⟩).lower ∧ (cell13110 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13110 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13110 ⟨32,by decide⟩).lower ∧ (cell13110 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13110 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13110 ⟨33,by decide⟩).lower ∧ (cell13110 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13110 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13110 ⟨34,by decide⟩).lower ∧ (cell13110 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13110 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13110 ⟨35,by decide⟩).lower ∧ (cell13110 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13110 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13110 ⟨36,by decide⟩).lower ∧ (cell13110 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13110 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13110 ⟨37,by decide⟩).lower ∧ (cell13110 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13110 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13110 ⟨38,by decide⟩).lower ∧ (cell13110 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13110 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13110 ⟨39,by decide⟩).lower ∧ (cell13110 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13110 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13110 ⟨40,by decide⟩).lower ∧ (cell13110 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13110 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13110 ⟨41,by decide⟩).lower ∧ (cell13110 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13110 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13110 ⟨42,by decide⟩).lower ∧ (cell13110 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13110 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13110 ⟨43,by decide⟩).lower ∧ (cell13110 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13110 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13110 ⟨44,by decide⟩).lower ∧ (cell13110 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13110 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13110 ⟨45,by decide⟩).lower ∧ (cell13110 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13110 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13110 ⟨46,by decide⟩).lower ∧ (cell13110 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13110 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13110 ⟨47,by decide⟩).lower ∧ (cell13110 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13110 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13110 ⟨48,by decide⟩).lower ∧ (cell13110 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13110 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13110 ⟨49,by decide⟩).lower ∧ (cell13110 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13110 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13110 ⟨50,by decide⟩).lower ∧ (cell13110 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13110 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13110 ⟨51,by decide⟩).lower ∧ (cell13110 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13110 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13110 ⟨52,by decide⟩).lower ∧ (cell13110 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13110 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13110 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13110 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13110,cell13110,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13110 i).lower ∧
    (cell13110 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13110 i).upper ≤ (0.532 : ℝ) ∧
    (cell13110 i).centre ≤ (0.1 : ℝ) ∧ (cell13110 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13110 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13110 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13110

/-! The local source numeric instances at 13110 have no network premises. -/
namespace BstLean.Part269.N13110
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13110)
open BstLean.Part268 (cell13110)

noncomputable def sourceNumerics13110 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13110 (cell13110 i)
      scalarRow13110.M scalarRow13110.H scalarRow13110.xi := by
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
    energy_allowance := scalarRow13110.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13110]
    centre_nonneg := (scalarRow13110.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13110])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13110
/-! Actual 13111 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13111 ≤ (1.035238585940 : ℝ) := by
  have hr : (114.503275062331 : ℝ) ≤ √(13111 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.503275062331 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13111 13111 (11 / 1000) ≤
    (0.008348118544 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13111) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.503275062331 : ℝ) ≤ √(13111 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13111)
  have hdiv : K / √(13111 : ℝ) ≤ K / 114.503275062331 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.503275062331 ≤ (0.008348118544 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13111.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13111 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13111 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13111 := gPlus_lower 13111
end BstLean.Part269.N13111

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13111
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035238585939 : ℝ) ≤ wn 13111 := by
  have hn : √(13111 : ℝ) ≤ 114.503275062332 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13111 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.503275062332 ≤ 2 / √(13111 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243850564 : ℝ) ≤ rhoBar 13111 BstLean.Part154.csC ∧
    rhoBar 13111 BstLean.Part154.csC ≤ 0.000243850942 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035238585939 : ℝ) / (1.295212 * 13111) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035238585940 : ℝ) / (1.29521 * 13111) := by gcongr
      _ ≤ (0.000243850942 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13111 BstLean.Part154.csC) ≤ 0.000975463232 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13111 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) ≤ 0.000186254718 ∧
    cc1 (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) ≤ 0.000118515171 ∧
    cc2 (rhoBar 13111 BstLean.Part154.csC) ≤ 0.000068799034 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13111 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13111 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13111 BstLean.Part154.csC * nuR (rhoBar 13111 BstLean.Part154.csC)) ≤ 0.000487716750 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243850942 : ℝ) * 0.000975463232 := by gcongr
      _ ≤ (0.000487716750 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13111 BstLean.Part154.csC) * nuR (rhoBar 13111 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975463232 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13111 BstLean.Part154.csC) * rhoBar 13111 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243850942 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243850942 / 2 + 0.399 * 0.000975463232 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186254718 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487716750 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118515171 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243850942 / 1.414213562 := by gcongr
      _ ≤ (0.000068799034 : ℝ) := by norm_num

end BstLean.Part269.N13111

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13111
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) ≤ 1.49813E-7 := by
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13111 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13111 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13111 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186254718 : ℝ) ^ 2 + 0.000118515171 ^ 2 + 3 * 0.000068799034 ^ 2 +
        2 * 0.797885 * 0.000186254718 * 0.000118515171 + 2 * 0.000186254718 * 0.000068799034 +
        4 * 0.797885 * 0.000118515171 * 0.000068799034 := by gcongr
    _ ≤ (1.49813E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13111 BstLean.Part154.csC Θ ≤ 0.002544053141 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13111 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13111 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13111 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035238585940 * 1.49813E-7 / (0.000243850564 : ℝ) := by gcongr
    _ ≤ 0.002544053141 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13111 BstLean.Part154.csC Θ ≤ 0.002821212621 + 0.000642843258 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13111 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13111 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035238585940 : ℝ) * ((2 * Θ * 0.000243850942 +
        (6863 / 10000) * 0.000243850942 * 13111 * 0.000975463232) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002821212621 + 0.000642843258 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13111 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13111 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13111 0.011 Θ ∧ gammaRatio 13111 0.011 Θ ≤ 0.000083829648 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13111 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035238585940 : ℝ) * 0.525 / ((1 - 0.011) * 13111) := by gcongr
      _ ≤ (0.000083829648 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13111 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13111 0.011 Θ) :=
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
    badAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13111 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13111 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13111 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13111 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13111 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13111 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13111 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13111 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13111 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13111 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035238585940 : ℝ) * 13111 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003170118203 + 0.003186896399 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13111

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13111
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13111 BstLean.Part154.csC) (piBar (rhoBar 13111 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13111 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13111 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13111 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13111 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13111 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13111 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13111 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13111 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13111 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13111 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051646281802 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13111) ≤ 0.010429724219 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13111 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035238585940)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010429724219 + 2 * 0.737676 / 13111) := by gcongr
    _ ≤ (0.051646281802 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13111 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13111

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13111
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521572282 : ℝ) ≤ plow 13111 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13111) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349838813)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335627900) : eMP 13111 0.011 xi bn ≤ 0.001150393505 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13111 : ℝ) * (1 - 0.011))) ≤ 0.000568855089 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335627900 / (13111 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568855089 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568855089 : ℝ) + 3.141593 * 0.052349838813 / (13111 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150393505 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349838813)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335627900) : PiBarMP 13111 12 0.011 xi bn ≤ 0.158678446422 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13111 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036546243309 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.871765596217 : ℝ) ≤ √((13111 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.503275062331 : ℝ) ≤ √(13111 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13111) ≤ 0.121676941164 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036546243309 + 0.052349838813 * 1.772454 / (2 * (113.871765596217 : ℝ))) * (1 + 0.001150393505) +
        8 / (13111 * 114.503275062331) + 0.121676941164 := by gcongr
    _ ≤ (0.158678446422 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349838813)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335627900) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280447153333) :
    parallelOracle 13111 0.011 xi bn cd ≤ 0.159637846073 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13111 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13111 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521572282 : ℝ) ≤ plow 13111 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.503275062331 : ℝ) ≤ √(13111 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280447153333 : ℝ) / (2 * 0.560521572282 * 114.503275062331)) * 0.158678446422 +
        0.280447153333 ^ 2 / (2 * 0.560521572282 * 114.503275062331) := by gcongr
    _ ≤ (0.159637846073 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349838813) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335627900)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280447153333) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13111 13111 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521572282 : ℝ) ≤ plow 13111 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.503275062331 : ℝ) ≤ √(13111 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13111 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13111 Θ 1.22 ≤ 0.011581332493 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.503275062331 := by gcongr <;> linarith
      _ ≤ (0.011581332493 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13111 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13111 13111 0.011 ≤ 0.008348118544 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13111 13111 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13111 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13111 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13111 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13111 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159637846073 + 0.011581332493 + (0.008348118544 : ℝ) *
        (1 + 2 * (0.280447153333 + 0.011581332493) / (0.560521572282 * 114.503275062331))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13111]

end BstLean.Part269.N13111

/-! The original eight local profiles supply actual 13111 moment certificates. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13111 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052349838813 ∧
    0 ≤ bN 13111 BstLean.Part154.csC (groupTheta g) ∧ bN 13111 BstLean.Part154.csC (groupTheta g) ≤ 0.001335627900 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13111 13111 0.011
      (momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13111 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13111 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13111 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228800871531 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13111 0.011
      (momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13111 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13111
/-! The actual computed-centre upper energy formula at 13111. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13111

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13111)
open BstLean.Part268 (cell13111)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084374259327
  | 2 => 0.085299263989
  | 3 => 0.086219934293
  | 4 => 0.087137106350
  | 5 => 0.088051808108
  | 6 => 0.088965289889
  | 7 => 0.089879058165
  | 8 => 0.090794912728
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13111 13111 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13111 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13111

/-! Actual upper energy certificates on all 43 source endpoints at 13111. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13111)
open BstLean.Part268 (cell13111)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13111 (gMinus 13111) (1 - (cell13111 i).lower) ≤ 1 ∧
    energyUpper 13111 (gMinus 13111) (BstLean.Part211.gPlus 13111)
      (finiteEnergy 13111 13111 0.011) (1 - (cell13111 i).lower) ≤
      (cell13111 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨10,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨11,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨12,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨13,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨14,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨15,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨16,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨17,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨18,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨19,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨20,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨21,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨22,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨23,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨24,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨25,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨26,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨27,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨28,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨29,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨30,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨31,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨32,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨33,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨34,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨35,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨36,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨37,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨38,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨39,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨40,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨41,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨42,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨43,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨44,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨45,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨46,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨47,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨48,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨49,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨50,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨51,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13111) (by norm_num)
        (q := 1 - (cell13111 ⟨52,by decide⟩).lower)
        (by norm_num [cell13111]) (by norm_num [cell13111])
      exact ⟨E.1,E.2.trans (by norm_num [cell13111])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13111

/-! Source-cell containment and simple scalar guards at 13111. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13111)
open BstLean.Part268 (cell13111)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13111 ⟨10,by decide⟩).lower ∧ (cell13111 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13111 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13111 ⟨11,by decide⟩).lower ∧ (cell13111 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13111 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13111 ⟨12,by decide⟩).lower ∧ (cell13111 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13111 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13111 ⟨13,by decide⟩).lower ∧ (cell13111 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13111 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13111 ⟨14,by decide⟩).lower ∧ (cell13111 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13111 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13111 ⟨15,by decide⟩).lower ∧ (cell13111 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13111 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13111 ⟨16,by decide⟩).lower ∧ (cell13111 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13111 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13111 ⟨17,by decide⟩).lower ∧ (cell13111 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13111 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13111 ⟨18,by decide⟩).lower ∧ (cell13111 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13111 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13111 ⟨19,by decide⟩).lower ∧ (cell13111 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13111 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13111 ⟨20,by decide⟩).lower ∧ (cell13111 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13111 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13111 ⟨21,by decide⟩).lower ∧ (cell13111 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13111 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13111 ⟨22,by decide⟩).lower ∧ (cell13111 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13111 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13111 ⟨23,by decide⟩).lower ∧ (cell13111 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13111 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13111 ⟨24,by decide⟩).lower ∧ (cell13111 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13111 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13111 ⟨25,by decide⟩).lower ∧ (cell13111 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13111 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13111 ⟨26,by decide⟩).lower ∧ (cell13111 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13111 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13111 ⟨27,by decide⟩).lower ∧ (cell13111 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13111 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13111 ⟨28,by decide⟩).lower ∧ (cell13111 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13111 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13111 ⟨29,by decide⟩).lower ∧ (cell13111 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13111 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13111 ⟨30,by decide⟩).lower ∧ (cell13111 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13111 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13111 ⟨31,by decide⟩).lower ∧ (cell13111 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13111 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13111 ⟨32,by decide⟩).lower ∧ (cell13111 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13111 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13111 ⟨33,by decide⟩).lower ∧ (cell13111 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13111 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13111 ⟨34,by decide⟩).lower ∧ (cell13111 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13111 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13111 ⟨35,by decide⟩).lower ∧ (cell13111 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13111 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13111 ⟨36,by decide⟩).lower ∧ (cell13111 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13111 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13111 ⟨37,by decide⟩).lower ∧ (cell13111 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13111 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13111 ⟨38,by decide⟩).lower ∧ (cell13111 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13111 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13111 ⟨39,by decide⟩).lower ∧ (cell13111 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13111 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13111 ⟨40,by decide⟩).lower ∧ (cell13111 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13111 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13111 ⟨41,by decide⟩).lower ∧ (cell13111 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13111 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13111 ⟨42,by decide⟩).lower ∧ (cell13111 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13111 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13111 ⟨43,by decide⟩).lower ∧ (cell13111 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13111 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13111 ⟨44,by decide⟩).lower ∧ (cell13111 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13111 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13111 ⟨45,by decide⟩).lower ∧ (cell13111 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13111 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13111 ⟨46,by decide⟩).lower ∧ (cell13111 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13111 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13111 ⟨47,by decide⟩).lower ∧ (cell13111 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13111 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13111 ⟨48,by decide⟩).lower ∧ (cell13111 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13111 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13111 ⟨49,by decide⟩).lower ∧ (cell13111 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13111 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13111 ⟨50,by decide⟩).lower ∧ (cell13111 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13111 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13111 ⟨51,by decide⟩).lower ∧ (cell13111 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13111 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13111 ⟨52,by decide⟩).lower ∧ (cell13111 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13111 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13111 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13111 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13111,cell13111,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13111 i).lower ∧
    (cell13111 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13111 i).upper ≤ (0.532 : ℝ) ∧
    (cell13111 i).centre ≤ (0.1 : ℝ) ∧ (cell13111 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13111 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13111 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13111

/-! The local source numeric instances at 13111 have no network premises. -/
namespace BstLean.Part269.N13111
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13111)
open BstLean.Part268 (cell13111)

noncomputable def sourceNumerics13111 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13111 (cell13111 i)
      scalarRow13111.M scalarRow13111.H scalarRow13111.xi := by
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
    energy_allowance := scalarRow13111.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13111]
    centre_nonneg := (scalarRow13111.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13111])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13111
/-! Actual 13112 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13112 ≤ (1.035237230527 : ℝ) := by
  have hr : (114.507641666397 : ℝ) ≤ √(13112 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.507641666397 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13112 13112 (11 / 1000) ≤
    (0.008347800197 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13112) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.507641666397 : ℝ) ≤ √(13112 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13112)
  have hdiv : K / √(13112 : ℝ) ≤ K / 114.507641666397 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.507641666397 ≤ (0.008347800197 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13112.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13112 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13112 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13112 := gPlus_lower 13112
end BstLean.Part269.N13112

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13112
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035237230526 : ℝ) ≤ wn 13112 := by
  have hn : √(13112 : ℝ) ≤ 114.507641666398 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13112 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.507641666398 ≤ 2 / √(13112 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243831647 : ℝ) ≤ rhoBar 13112 BstLean.Part154.csC ∧
    rhoBar 13112 BstLean.Part154.csC ≤ 0.000243832025 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035237230526 : ℝ) / (1.295212 * 13112) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035237230527 : ℝ) / (1.29521 * 13112) := by gcongr
      _ ≤ (0.000243832025 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13112 BstLean.Part154.csC) ≤ 0.000975387555 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13112 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) ≤ 0.000186240269 ∧
    cc1 (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) ≤ 0.000118505977 ∧
    cc2 (rhoBar 13112 BstLean.Part154.csC) ≤ 0.000068793697 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13112 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13112 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13112 BstLean.Part154.csC * nuR (rhoBar 13112 BstLean.Part154.csC)) ≤ 0.000487678914 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243832025 : ℝ) * 0.000975387555 := by gcongr
      _ ≤ (0.000487678914 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13112 BstLean.Part154.csC) * nuR (rhoBar 13112 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975387555 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13112 BstLean.Part154.csC) * rhoBar 13112 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243832025 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243832025 / 2 + 0.399 * 0.000975387555 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186240269 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487678914 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118505977 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243832025 / 1.414213562 := by gcongr
      _ ≤ (0.000068793697 : ℝ) := by norm_num

end BstLean.Part269.N13112

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13112
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) ≤ 1.49790E-7 := by
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13112 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13112 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13112 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186240269 : ℝ) ^ 2 + 0.000118505977 ^ 2 + 3 * 0.000068793697 ^ 2 +
        2 * 0.797885 * 0.000186240269 * 0.000118505977 + 2 * 0.000186240269 * 0.000068793697 +
        4 * 0.797885 * 0.000118505977 * 0.000068793697 := by gcongr
    _ ≤ (1.49790E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13112 BstLean.Part154.csC Θ ≤ 0.002543856578 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13112 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13112 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13112 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035237230527 * 1.49790E-7 / (0.000243831647 : ℝ) := by gcongr
    _ ≤ 0.002543856578 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13112 BstLean.Part154.csC Θ ≤ 0.002820986360 + 0.000642792547 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13112 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13112 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035237230527 : ℝ) * ((2 * Θ * 0.000243832025 +
        (6863 / 10000) * 0.000243832025 * 13112 * 0.000975387555) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002820986360 + 0.000642792547 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13112 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13112 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13112 0.011 Θ ∧ gammaRatio 13112 0.011 Θ ≤ 0.000083823145 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13112 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035237230527 : ℝ) * 0.525 / ((1 - 0.011) * 13112) := by gcongr
      _ ≤ (0.000083823145 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13112 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13112 0.011 Θ) :=
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
    badAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13112 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13112 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13112 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13112 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13112 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13112 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13112 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13112 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13112 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13112 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035237230527 : ℝ) * 13112 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003169891942 + 0.003186649125 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13112

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13112
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13112 BstLean.Part154.csC) (piBar (rhoBar 13112 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13112 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13112 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13112 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13112 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13112 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13112 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13112 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13112 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13112 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13112 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051644291317 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13112) ≤ 0.010429326495 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13112 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035237230527)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010429326495 + 2 * 0.737676 / 13112) := by gcongr
    _ ≤ (0.051644291317 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13112 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13112

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13112
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521614711 : ℝ) ≤ plow 13112 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13112) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349482733)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335524704) : eMP 13112 0.011 xi bn ≤ 0.001150305115 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13112 : ℝ) * (1 - 0.011))) ≤ 0.000568811421 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335524704 / (13112 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568811421 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568811421 : ℝ) + 3.141593 * 0.052349482733 / (13112 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150305115 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349482733)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335524704) : PiBarMP 13112 12 0.011 xi bn ≤ 0.158672370714 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13112 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036544831427 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.876108117550 : ℝ) ≤ √((13112 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.507641666397 : ℝ) ≤ √(13112 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13112) ≤ 0.121672301167 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036544831427 + 0.052349482733 * 1.772454 / (2 * (113.876108117550 : ℝ))) * (1 + 0.001150305115) +
        8 / (13112 * 114.507641666397) + 0.121672301167 := by gcongr
    _ ≤ (0.158672370714 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349482733)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335524704) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280444384703) :
    parallelOracle 13112 0.011 xi bn cd ≤ 0.159631704914 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13112 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13112 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521614711 : ℝ) ≤ plow 13112 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.507641666397 : ℝ) ≤ √(13112 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280444384703 : ℝ) / (2 * 0.560521614711 * 114.507641666397)) * 0.158672370714 +
        0.280444384703 ^ 2 / (2 * 0.560521614711 * 114.507641666397) := by gcongr
    _ ≤ (0.159631704914 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349482733) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335524704)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280444384703) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13112 13112 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521614711 : ℝ) ≤ plow 13112 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.507641666397 : ℝ) ≤ √(13112 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13112 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13112 Θ 1.22 ≤ 0.011580890854 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.507641666397 := by gcongr <;> linarith
      _ ≤ (0.011580890854 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13112 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13112 13112 0.011 ≤ 0.008347800197 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13112 13112 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13112 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13112 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13112 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13112 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159631704914 + 0.011580890854 + (0.008347800197 : ℝ) *
        (1 + 2 * (0.280444384703 + 0.011580890854) / (0.560521614711 * 114.507641666397))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13112]

end BstLean.Part269.N13112

/-! The original eight local profiles supply actual 13112 moment certificates. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13112 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052349482733 ∧
    0 ≤ bN 13112 BstLean.Part154.csC (groupTheta g) ∧ bN 13112 BstLean.Part154.csC (groupTheta g) ≤ 0.001335524704 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13112 13112 0.011
      (momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13112 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13112 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13112 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228800093386 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13112 0.011
      (momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13112 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13112
/-! The actual computed-centre upper energy formula at 13112. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13112

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13112)
open BstLean.Part268 (cell13112)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084371726327
  | 2 => 0.085296699391
  | 3 => 0.086217333553
  | 4 => 0.087134463840
  | 5 => 0.088049116919
  | 6 => 0.088962541601
  | 7 => 0.089876242592
  | 8 => 0.090792017630
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13112 13112 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13112 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13112

/-! Actual upper energy certificates on all 43 source endpoints at 13112. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13112)
open BstLean.Part268 (cell13112)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13112 (gMinus 13112) (1 - (cell13112 i).lower) ≤ 1 ∧
    energyUpper 13112 (gMinus 13112) (BstLean.Part211.gPlus 13112)
      (finiteEnergy 13112 13112 0.011) (1 - (cell13112 i).lower) ≤
      (cell13112 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨10,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨11,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨12,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨13,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨14,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨15,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨16,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨17,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨18,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨19,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨20,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨21,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨22,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨23,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨24,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨25,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨26,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨27,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨28,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨29,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨30,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨31,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨32,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨33,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨34,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨35,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨36,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨37,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨38,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨39,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨40,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨41,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨42,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨43,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨44,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨45,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨46,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨47,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨48,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨49,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨50,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨51,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13112) (by norm_num)
        (q := 1 - (cell13112 ⟨52,by decide⟩).lower)
        (by norm_num [cell13112]) (by norm_num [cell13112])
      exact ⟨E.1,E.2.trans (by norm_num [cell13112])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13112

/-! Source-cell containment and simple scalar guards at 13112. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13112)
open BstLean.Part268 (cell13112)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13112 ⟨10,by decide⟩).lower ∧ (cell13112 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13112 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13112 ⟨11,by decide⟩).lower ∧ (cell13112 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13112 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13112 ⟨12,by decide⟩).lower ∧ (cell13112 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13112 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13112 ⟨13,by decide⟩).lower ∧ (cell13112 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13112 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13112 ⟨14,by decide⟩).lower ∧ (cell13112 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13112 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13112 ⟨15,by decide⟩).lower ∧ (cell13112 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13112 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13112 ⟨16,by decide⟩).lower ∧ (cell13112 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13112 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13112 ⟨17,by decide⟩).lower ∧ (cell13112 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13112 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13112 ⟨18,by decide⟩).lower ∧ (cell13112 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13112 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13112 ⟨19,by decide⟩).lower ∧ (cell13112 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13112 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13112 ⟨20,by decide⟩).lower ∧ (cell13112 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13112 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13112 ⟨21,by decide⟩).lower ∧ (cell13112 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13112 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13112 ⟨22,by decide⟩).lower ∧ (cell13112 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13112 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13112 ⟨23,by decide⟩).lower ∧ (cell13112 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13112 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13112 ⟨24,by decide⟩).lower ∧ (cell13112 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13112 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13112 ⟨25,by decide⟩).lower ∧ (cell13112 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13112 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13112 ⟨26,by decide⟩).lower ∧ (cell13112 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13112 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13112 ⟨27,by decide⟩).lower ∧ (cell13112 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13112 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13112 ⟨28,by decide⟩).lower ∧ (cell13112 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13112 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13112 ⟨29,by decide⟩).lower ∧ (cell13112 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13112 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13112 ⟨30,by decide⟩).lower ∧ (cell13112 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13112 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13112 ⟨31,by decide⟩).lower ∧ (cell13112 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13112 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13112 ⟨32,by decide⟩).lower ∧ (cell13112 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13112 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13112 ⟨33,by decide⟩).lower ∧ (cell13112 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13112 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13112 ⟨34,by decide⟩).lower ∧ (cell13112 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13112 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13112 ⟨35,by decide⟩).lower ∧ (cell13112 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13112 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13112 ⟨36,by decide⟩).lower ∧ (cell13112 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13112 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13112 ⟨37,by decide⟩).lower ∧ (cell13112 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13112 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13112 ⟨38,by decide⟩).lower ∧ (cell13112 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13112 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13112 ⟨39,by decide⟩).lower ∧ (cell13112 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13112 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13112 ⟨40,by decide⟩).lower ∧ (cell13112 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13112 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13112 ⟨41,by decide⟩).lower ∧ (cell13112 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13112 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13112 ⟨42,by decide⟩).lower ∧ (cell13112 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13112 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13112 ⟨43,by decide⟩).lower ∧ (cell13112 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13112 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13112 ⟨44,by decide⟩).lower ∧ (cell13112 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13112 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13112 ⟨45,by decide⟩).lower ∧ (cell13112 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13112 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13112 ⟨46,by decide⟩).lower ∧ (cell13112 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13112 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13112 ⟨47,by decide⟩).lower ∧ (cell13112 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13112 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13112 ⟨48,by decide⟩).lower ∧ (cell13112 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13112 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13112 ⟨49,by decide⟩).lower ∧ (cell13112 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13112 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13112 ⟨50,by decide⟩).lower ∧ (cell13112 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13112 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13112 ⟨51,by decide⟩).lower ∧ (cell13112 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13112 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13112 ⟨52,by decide⟩).lower ∧ (cell13112 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13112 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13112 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13112 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13112,cell13112,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13112 i).lower ∧
    (cell13112 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13112 i).upper ≤ (0.532 : ℝ) ∧
    (cell13112 i).centre ≤ (0.1 : ℝ) ∧ (cell13112 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13112 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13112 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13112

/-! The local source numeric instances at 13112 have no network premises. -/
namespace BstLean.Part269.N13112
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13112)
open BstLean.Part268 (cell13112)

noncomputable def sourceNumerics13112 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13112 (cell13112 i)
      scalarRow13112.M scalarRow13112.H scalarRow13112.xi := by
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
    energy_allowance := scalarRow13112.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13112]
    centre_nonneg := (scalarRow13112.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13112])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13112