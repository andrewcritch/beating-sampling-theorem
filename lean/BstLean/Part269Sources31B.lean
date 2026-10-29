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
import BstLean.Part269Direction31
import BstLean.Part269Shared31
import BstLean.Part269Finite
import BstLean.Part269Rows31
import BstLean.Part269Source
/-! Actual 13138 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13138 ≤ (1.035202044447 : ℝ) := by
  have hr : (114.621114983235 : ℝ) ≤ √(13138 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.621114983235 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13138 13138 (11 / 1000) ≤
    (0.008339535929 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13138) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.621114983235 : ℝ) ≤ √(13138 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13138)
  have hdiv : K / √(13138 : ℝ) ≤ K / 114.621114983235 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.621114983235 ≤ (0.008339535929 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13138.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13138 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13138 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13138 := gPlus_lower 13138
end BstLean.Part269.N13138

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13138
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035202044446 : ℝ) ≤ wn 13138 := by
  have hn : √(13138 : ℝ) ≤ 114.621114983236 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13138 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.621114983236 ≤ 2 / √(13138 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243340835 : ℝ) ≤ rhoBar 13138 BstLean.Part154.csC ∧
    rhoBar 13138 BstLean.Part154.csC ≤ 0.000243341212 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035202044446 : ℝ) / (1.295212 * 13138) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035202044447 : ℝ) / (1.29521 * 13138) := by gcongr
      _ ≤ (0.000243341212 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13138 BstLean.Part154.csC) ≤ 0.000973424063 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13138 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) ≤ 0.000185865366 ∧
    cc1 (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) ≤ 0.000118267427 ∧
    cc2 (rhoBar 13138 BstLean.Part154.csC) ≤ 0.000068655221 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13138 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13138 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13138 BstLean.Part154.csC * nuR (rhoBar 13138 BstLean.Part154.csC)) ≤ 0.000486697228 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243341212 : ℝ) * 0.000973424063 := by gcongr
      _ ≤ (0.000486697228 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13138 BstLean.Part154.csC) * nuR (rhoBar 13138 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973424063 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13138 BstLean.Part154.csC) * rhoBar 13138 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243341212 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243341212 / 2 + 0.399 * 0.000973424063 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185865366 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486697228 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118267427 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243341212 / 1.414213562 := by gcongr
      _ ≤ (0.000068655221 : ℝ) := by norm_num

end BstLean.Part269.N13138

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13138
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) ≤ 1.49188E-7 := by
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13138 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13138 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13138 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185865366 : ℝ) ^ 2 + 0.000118267427 ^ 2 + 3 * 0.000068655221 ^ 2 +
        2 * 0.797885 * 0.000185865366 * 0.000118267427 + 2 * 0.000185865366 * 0.000068655221 +
        4 * 0.797885 * 0.000118267427 * 0.000068655221 := by gcongr
    _ ≤ (1.49188E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13138 BstLean.Part154.csC Θ ≤ 0.002538656903 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13138 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13138 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13138 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035202044447 * 1.49188E-7 / (0.000243340835 : ℝ) := by gcongr
    _ ≤ 0.002538656903 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13138 BstLean.Part154.csC Θ ≤ 0.002815116233 + 0.000641476857 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13138 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13138 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035202044447 : ℝ) * ((2 * Θ * 0.000243341212 +
        (6863 / 10000) * 0.000243341212 * 13138 * 0.000973424063) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002815116233 + 0.000641476857 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13138 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13138 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13138 0.011 Θ ∧ gammaRatio 13138 0.011 Θ ≤ 0.000083654416 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13138 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035202044447 : ℝ) * 0.525 / ((1 - 0.011) * 13138) := by gcongr
      _ ≤ (0.000083654416 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13138 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13138 0.011 Θ) :=
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
    badAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13138 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13138 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13138 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13138 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13138 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13138 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13138 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13138 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13138 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13138 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035202044447 : ℝ) * 13138 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003164204719 + 0.003180133760 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13138

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13138
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13138 BstLean.Part154.csC) (piBar (rhoBar 13138 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13138 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13138 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13138 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13138 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13138 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13138 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13138 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13138 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13138 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13138 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051592619013 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13138) ≤ 0.010419001606 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13138 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035202044447)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010419001606 + 2 * 0.737676 / 13138) := by gcongr
    _ ≤ (0.051592619013 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13138 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13138

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13138
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522715595 : ℝ) ≤ plow 13138 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13138) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340374943)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332794875) : eMP 13138 0.011 xi bn ≤ 0.001147989483 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13138 : ℝ) * (1 - 0.011))) ≤ 0.000567667255 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332794875 / (13138 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567667255 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567667255 : ℝ) + 3.141593 * 0.052340374943 / (13138 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147989483 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340374943)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332794875) : PiBarMP 13138 12 0.011 xi bn ≤ 0.158513929720 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13138 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036507463279 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.988955605356 : ℝ) ≤ √((13138 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.621114983235 : ℝ) ≤ √(13138 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13138) ≤ 0.121551847274 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036507463279 + 0.052340374943 * 1.772454 / (2 * (113.988955605356 : ℝ))) * (1 + 0.001147989483) +
        8 / (13138 * 114.621114983235) + 0.121551847274 := by gcongr
    _ ≤ (0.158513929720 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340374943)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332794875) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280372808154) :
    parallelOracle 13138 0.011 xi bn cd ≤ 0.159471565816 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13138 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13138 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522715595 : ℝ) ≤ plow 13138 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.621114983235 : ℝ) ≤ √(13138 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280372808154 : ℝ) / (2 * 0.560522715595 * 114.621114983235)) * 0.158513929720 +
        0.280372808154 ^ 2 / (2 * 0.560522715595 * 114.621114983235) := by gcongr
    _ ≤ (0.159471565816 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340374943) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332794875)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280372808154) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13138 13138 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522715595 : ℝ) ≤ plow 13138 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.621114983235 : ℝ) ≤ √(13138 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13138 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13138 Θ 1.22 ≤ 0.011569425932 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.621114983235 := by gcongr <;> linarith
      _ ≤ (0.011569425932 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13138 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13138 13138 0.011 ≤ 0.008339535929 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13138 13138 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13138 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13138 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13138 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13138 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159471565816 + 0.011569425932 + (0.008339535929 : ℝ) *
        (1 + 2 * (0.280372808154 + 0.011569425932) / (0.560522715595 * 114.621114983235))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13138]

end BstLean.Part269.N13138

/-! The original eight local profiles supply actual 13138 moment certificates. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13138 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052340374943 ∧
    0 ≤ bN 13138 BstLean.Part154.csC (groupTheta g) ∧ bN 13138 BstLean.Part154.csC (groupTheta g) ≤ 0.001332794875 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13138 13138 0.011
      (momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13138 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13138 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13138 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228780189141 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13138 0.011
      (momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13138 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13138
/-! The actual computed-centre upper energy formula at 13138. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13138

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13138)
open BstLean.Part268 (cell13138)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084306122574
  | 2 => 0.085230282660
  | 3 => 0.086149987754
  | 4 => 0.087066045188
  | 5 => 0.087979448791
  | 6 => 0.088891408689
  | 7 => 0.089803384323
  | 8 => 0.090717120787
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13138 13138 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13138 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13138

/-! Actual upper energy certificates on all 43 source endpoints at 13138. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13138)
open BstLean.Part268 (cell13138)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13138 (gMinus 13138) (1 - (cell13138 i).lower) ≤ 1 ∧
    energyUpper 13138 (gMinus 13138) (BstLean.Part211.gPlus 13138)
      (finiteEnergy 13138 13138 0.011) (1 - (cell13138 i).lower) ≤
      (cell13138 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨10,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨11,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨12,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨13,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨14,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨15,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨16,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨17,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨18,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨19,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨20,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨21,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨22,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨23,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨24,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨25,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨26,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨27,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨28,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨29,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨30,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨31,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨32,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨33,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨34,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨35,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨36,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨37,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨38,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨39,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨40,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨41,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨42,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨43,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨44,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨45,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨46,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨47,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨48,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨49,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨50,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨51,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13138) (by norm_num)
        (q := 1 - (cell13138 ⟨52,by decide⟩).lower)
        (by norm_num [cell13138]) (by norm_num [cell13138])
      exact ⟨E.1,E.2.trans (by norm_num [cell13138])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13138

/-! Source-cell containment and simple scalar guards at 13138. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13138)
open BstLean.Part268 (cell13138)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13138 ⟨10,by decide⟩).lower ∧ (cell13138 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13138 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13138 ⟨11,by decide⟩).lower ∧ (cell13138 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13138 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13138 ⟨12,by decide⟩).lower ∧ (cell13138 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13138 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13138 ⟨13,by decide⟩).lower ∧ (cell13138 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13138 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13138 ⟨14,by decide⟩).lower ∧ (cell13138 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13138 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13138 ⟨15,by decide⟩).lower ∧ (cell13138 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13138 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13138 ⟨16,by decide⟩).lower ∧ (cell13138 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13138 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13138 ⟨17,by decide⟩).lower ∧ (cell13138 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13138 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13138 ⟨18,by decide⟩).lower ∧ (cell13138 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13138 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13138 ⟨19,by decide⟩).lower ∧ (cell13138 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13138 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13138 ⟨20,by decide⟩).lower ∧ (cell13138 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13138 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13138 ⟨21,by decide⟩).lower ∧ (cell13138 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13138 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13138 ⟨22,by decide⟩).lower ∧ (cell13138 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13138 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13138 ⟨23,by decide⟩).lower ∧ (cell13138 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13138 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13138 ⟨24,by decide⟩).lower ∧ (cell13138 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13138 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13138 ⟨25,by decide⟩).lower ∧ (cell13138 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13138 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13138 ⟨26,by decide⟩).lower ∧ (cell13138 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13138 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13138 ⟨27,by decide⟩).lower ∧ (cell13138 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13138 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13138 ⟨28,by decide⟩).lower ∧ (cell13138 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13138 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13138 ⟨29,by decide⟩).lower ∧ (cell13138 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13138 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13138 ⟨30,by decide⟩).lower ∧ (cell13138 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13138 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13138 ⟨31,by decide⟩).lower ∧ (cell13138 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13138 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13138 ⟨32,by decide⟩).lower ∧ (cell13138 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13138 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13138 ⟨33,by decide⟩).lower ∧ (cell13138 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13138 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13138 ⟨34,by decide⟩).lower ∧ (cell13138 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13138 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13138 ⟨35,by decide⟩).lower ∧ (cell13138 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13138 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13138 ⟨36,by decide⟩).lower ∧ (cell13138 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13138 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13138 ⟨37,by decide⟩).lower ∧ (cell13138 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13138 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13138 ⟨38,by decide⟩).lower ∧ (cell13138 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13138 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13138 ⟨39,by decide⟩).lower ∧ (cell13138 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13138 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13138 ⟨40,by decide⟩).lower ∧ (cell13138 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13138 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13138 ⟨41,by decide⟩).lower ∧ (cell13138 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13138 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13138 ⟨42,by decide⟩).lower ∧ (cell13138 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13138 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13138 ⟨43,by decide⟩).lower ∧ (cell13138 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13138 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13138 ⟨44,by decide⟩).lower ∧ (cell13138 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13138 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13138 ⟨45,by decide⟩).lower ∧ (cell13138 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13138 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13138 ⟨46,by decide⟩).lower ∧ (cell13138 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13138 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13138 ⟨47,by decide⟩).lower ∧ (cell13138 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13138 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13138 ⟨48,by decide⟩).lower ∧ (cell13138 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13138 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13138 ⟨49,by decide⟩).lower ∧ (cell13138 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13138 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13138 ⟨50,by decide⟩).lower ∧ (cell13138 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13138 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13138 ⟨51,by decide⟩).lower ∧ (cell13138 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13138 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13138 ⟨52,by decide⟩).lower ∧ (cell13138 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13138 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13138 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13138 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13138,cell13138,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13138 i).lower ∧
    (cell13138 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13138 i).upper ≤ (0.532 : ℝ) ∧
    (cell13138 i).centre ≤ (0.1 : ℝ) ∧ (cell13138 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13138 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13138 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13138

/-! The local source numeric instances at 13138 have no network premises. -/
namespace BstLean.Part269.N13138
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13138)
open BstLean.Part268 (cell13138)

noncomputable def sourceNumerics13138 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13138 (cell13138 i)
      scalarRow13138.M scalarRow13138.H scalarRow13138.xi := by
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
    energy_allowance := scalarRow13138.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13138]
    centre_nonneg := (scalarRow13138.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13138])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13138
/-! Actual 13139 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13139 ≤ (1.035200693234 : ℝ) := by
  have hr : (114.625477098243 : ℝ) ≤ √(13139 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.625477098243 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13139 13139 (11 / 1000) ≤
    (0.008339218562 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13139) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.625477098243 : ℝ) ≤ √(13139 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13139)
  have hdiv : K / √(13139 : ℝ) ≤ K / 114.625477098243 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.625477098243 ≤ (0.008339218562 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13139.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13139 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13139 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13139 := gPlus_lower 13139
end BstLean.Part269.N13139

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13139
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035200693233 : ℝ) ≤ wn 13139 := by
  have hn : √(13139 : ℝ) ≤ 114.625477098244 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13139 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.625477098244 ≤ 2 / √(13139 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243321997 : ℝ) ≤ rhoBar 13139 BstLean.Part154.csC ∧
    rhoBar 13139 BstLean.Part154.csC ≤ 0.000243322374 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035200693233 : ℝ) / (1.295212 * 13139) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035200693234 : ℝ) / (1.29521 * 13139) := by gcongr
      _ ≤ (0.000243322374 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13139 BstLean.Part154.csC) ≤ 0.000973348702 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13139 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) ≤ 0.000185850977 ∧
    cc1 (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) ≤ 0.000118258271 ∧
    cc2 (rhoBar 13139 BstLean.Part154.csC) ≤ 0.000068649906 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13139 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13139 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13139 BstLean.Part154.csC * nuR (rhoBar 13139 BstLean.Part154.csC)) ≤ 0.000486659550 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243322374 : ℝ) * 0.000973348702 := by gcongr
      _ ≤ (0.000486659550 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13139 BstLean.Part154.csC) * nuR (rhoBar 13139 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973348702 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13139 BstLean.Part154.csC) * rhoBar 13139 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243322374 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243322374 / 2 + 0.399 * 0.000973348702 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185850977 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486659550 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118258271 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243322374 / 1.414213562 := by gcongr
      _ ≤ (0.000068649906 : ℝ) := by norm_num

end BstLean.Part269.N13139

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13139
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) ≤ 1.49165E-7 := by
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13139 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13139 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13139 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185850977 : ℝ) ^ 2 + 0.000118258271 ^ 2 + 3 * 0.000068649906 ^ 2 +
        2 * 0.797885 * 0.000185850977 * 0.000118258271 + 2 * 0.000185850977 * 0.000068649906 +
        4 * 0.797885 * 0.000118258271 * 0.000068649906 := by gcongr
    _ ≤ (1.49165E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13139 BstLean.Part154.csC Θ ≤ 0.002538458723 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13139 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13139 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13139 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035200693234 * 1.49165E-7 / (0.000243321997 : ℝ) := by gcongr
    _ ≤ 0.002538458723 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13139 BstLean.Part154.csC Θ ≤ 0.002814890944 + 0.000641426361 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13139 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13139 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035200693234 : ℝ) * ((2 * Θ * 0.000243322374 +
        (6863 / 10000) * 0.000243322374 * 13139 * 0.000973348702) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002814890944 + 0.000641426361 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13139 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13139 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13139 0.011 Θ ∧ gammaRatio 13139 0.011 Θ ≤ 0.000083647940 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13139 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035200693234 : ℝ) * 0.525 / ((1 - 0.011) * 13139) := by gcongr
      _ ≤ (0.000083647940 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13139 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13139 0.011 Θ) :=
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
    badAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13139 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13139 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13139 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13139 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13139 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13139 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13139 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13139 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13139 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13139 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035200693234 : ℝ) * 13139 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003163979430 + 0.003179885084 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13139

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13139
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13139 BstLean.Part154.csC) (piBar (rhoBar 13139 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13139 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13139 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13139 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13139 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13139 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13139 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13139 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13139 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13139 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13139 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051590634702 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13139) ≤ 0.010418605107 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13139 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035200693234)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010418605107 + 2 * 0.737676 / 13139) := by gcongr
    _ ≤ (0.051590634702 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13139 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13139

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13139
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522757850 : ℝ) ≤ plow 13139 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13139) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340019100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332690830) : eMP 13139 0.011 xi bn ≤ 0.001147900914 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13139 : ℝ) * (1 - 0.011))) ≤ 0.000567623495 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332690830 / (13139 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567623495 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567623495 : ℝ) + 3.141593 * 0.052340019100 / (13139 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147900914 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340019100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332690830) : PiBarMP 13139 12 0.011 xi bn ≤ 0.158507855223 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13139 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036506038268 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.993293662390 : ℝ) ≤ √((13139 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.625477098243 : ℝ) ≤ √(13139 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13139) ≤ 0.121547221573 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036506038268 + 0.052340019100 * 1.772454 / (2 * (113.993293662390 : ℝ))) * (1 + 0.001147900914) +
        8 / (13139 * 114.625477098243) + 0.121547221573 := by gcongr
    _ ≤ (0.158507855223 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340019100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332690830) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280370046145) :
    parallelOracle 13139 0.011 xi bn cd ≤ 0.159465426090 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13139 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13139 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522757850 : ℝ) ≤ plow 13139 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.625477098243 : ℝ) ≤ √(13139 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280370046145 : ℝ) / (2 * 0.560522757850 * 114.625477098243)) * 0.158507855223 +
        0.280370046145 ^ 2 / (2 * 0.560522757850 * 114.625477098243) := by gcongr
    _ ≤ (0.159465426090 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340019100) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332690830)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280370046145) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13139 13139 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522757850 : ℝ) ≤ plow 13139 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.625477098243 : ℝ) ≤ √(13139 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13139 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13139 Θ 1.22 ≤ 0.011568985653 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.625477098243 := by gcongr <;> linarith
      _ ≤ (0.011568985653 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13139 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13139 13139 0.011 ≤ 0.008339218562 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13139 13139 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13139 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13139 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13139 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13139 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159465426090 + 0.011568985653 + (0.008339218562 : ℝ) *
        (1 + 2 * (0.280370046145 + 0.011568985653) / (0.560522757850 * 114.625477098243))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13139]

end BstLean.Part269.N13139

/-! The original eight local profiles supply actual 13139 moment certificates. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13139 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052340019100 ∧
    0 ≤ bN 13139 BstLean.Part154.csC (groupTheta g) ∧ bN 13139 BstLean.Part154.csC (groupTheta g) ≤ 0.001332690830 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13139 13139 0.011
      (momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13139 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13139 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13139 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228779411443 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13139 0.011
      (momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13139 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13139
/-! The actual computed-centre upper energy formula at 13139. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13139

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13139)
open BstLean.Part268 (cell13139)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084303609050
  | 2 => 0.085227738194
  | 3 => 0.086147407959
  | 4 => 0.087063424630
  | 5 => 0.087976780791
  | 6 => 0.088888685102
  | 7 => 0.089800595291
  | 8 => 0.090714254454
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13139 13139 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13139 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13139

/-! Actual upper energy certificates on all 43 source endpoints at 13139. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13139)
open BstLean.Part268 (cell13139)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13139 (gMinus 13139) (1 - (cell13139 i).lower) ≤ 1 ∧
    energyUpper 13139 (gMinus 13139) (BstLean.Part211.gPlus 13139)
      (finiteEnergy 13139 13139 0.011) (1 - (cell13139 i).lower) ≤
      (cell13139 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨10,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨11,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨12,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨13,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨14,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨15,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨16,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨17,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨18,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨19,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨20,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨21,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨22,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨23,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨24,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨25,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨26,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨27,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨28,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨29,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨30,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨31,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨32,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨33,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨34,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨35,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨36,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨37,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨38,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨39,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨40,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨41,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨42,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨43,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨44,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨45,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨46,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨47,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨48,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨49,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨50,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨51,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13139) (by norm_num)
        (q := 1 - (cell13139 ⟨52,by decide⟩).lower)
        (by norm_num [cell13139]) (by norm_num [cell13139])
      exact ⟨E.1,E.2.trans (by norm_num [cell13139])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13139

/-! Source-cell containment and simple scalar guards at 13139. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13139)
open BstLean.Part268 (cell13139)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13139 ⟨10,by decide⟩).lower ∧ (cell13139 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13139 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13139 ⟨11,by decide⟩).lower ∧ (cell13139 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13139 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13139 ⟨12,by decide⟩).lower ∧ (cell13139 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13139 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13139 ⟨13,by decide⟩).lower ∧ (cell13139 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13139 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13139 ⟨14,by decide⟩).lower ∧ (cell13139 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13139 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13139 ⟨15,by decide⟩).lower ∧ (cell13139 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13139 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13139 ⟨16,by decide⟩).lower ∧ (cell13139 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13139 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13139 ⟨17,by decide⟩).lower ∧ (cell13139 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13139 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13139 ⟨18,by decide⟩).lower ∧ (cell13139 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13139 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13139 ⟨19,by decide⟩).lower ∧ (cell13139 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13139 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13139 ⟨20,by decide⟩).lower ∧ (cell13139 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13139 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13139 ⟨21,by decide⟩).lower ∧ (cell13139 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13139 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13139 ⟨22,by decide⟩).lower ∧ (cell13139 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13139 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13139 ⟨23,by decide⟩).lower ∧ (cell13139 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13139 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13139 ⟨24,by decide⟩).lower ∧ (cell13139 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13139 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13139 ⟨25,by decide⟩).lower ∧ (cell13139 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13139 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13139 ⟨26,by decide⟩).lower ∧ (cell13139 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13139 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13139 ⟨27,by decide⟩).lower ∧ (cell13139 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13139 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13139 ⟨28,by decide⟩).lower ∧ (cell13139 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13139 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13139 ⟨29,by decide⟩).lower ∧ (cell13139 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13139 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13139 ⟨30,by decide⟩).lower ∧ (cell13139 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13139 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13139 ⟨31,by decide⟩).lower ∧ (cell13139 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13139 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13139 ⟨32,by decide⟩).lower ∧ (cell13139 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13139 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13139 ⟨33,by decide⟩).lower ∧ (cell13139 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13139 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13139 ⟨34,by decide⟩).lower ∧ (cell13139 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13139 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13139 ⟨35,by decide⟩).lower ∧ (cell13139 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13139 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13139 ⟨36,by decide⟩).lower ∧ (cell13139 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13139 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13139 ⟨37,by decide⟩).lower ∧ (cell13139 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13139 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13139 ⟨38,by decide⟩).lower ∧ (cell13139 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13139 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13139 ⟨39,by decide⟩).lower ∧ (cell13139 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13139 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13139 ⟨40,by decide⟩).lower ∧ (cell13139 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13139 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13139 ⟨41,by decide⟩).lower ∧ (cell13139 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13139 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13139 ⟨42,by decide⟩).lower ∧ (cell13139 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13139 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13139 ⟨43,by decide⟩).lower ∧ (cell13139 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13139 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13139 ⟨44,by decide⟩).lower ∧ (cell13139 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13139 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13139 ⟨45,by decide⟩).lower ∧ (cell13139 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13139 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13139 ⟨46,by decide⟩).lower ∧ (cell13139 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13139 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13139 ⟨47,by decide⟩).lower ∧ (cell13139 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13139 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13139 ⟨48,by decide⟩).lower ∧ (cell13139 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13139 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13139 ⟨49,by decide⟩).lower ∧ (cell13139 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13139 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13139 ⟨50,by decide⟩).lower ∧ (cell13139 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13139 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13139 ⟨51,by decide⟩).lower ∧ (cell13139 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13139 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13139 ⟨52,by decide⟩).lower ∧ (cell13139 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13139 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13139 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13139 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13139,cell13139,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13139 i).lower ∧
    (cell13139 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13139 i).upper ≤ (0.532 : ℝ) ∧
    (cell13139 i).centre ≤ (0.1 : ℝ) ∧ (cell13139 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13139 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13139 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13139

/-! The local source numeric instances at 13139 have no network premises. -/
namespace BstLean.Part269.N13139
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13139)
open BstLean.Part268 (cell13139)

noncomputable def sourceNumerics13139 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13139 (cell13139 i)
      scalarRow13139.M scalarRow13139.H scalarRow13139.xi := by
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
    energy_allowance := scalarRow13139.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13139]
    centre_nonneg := (scalarRow13139.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13139])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13139
/-! Actual 13140 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13140 ≤ (1.035199342176 : ℝ) := by
  have hr : (114.629839047256 : ℝ) ≤ √(13140 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.629839047256 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13140 13140 (11 / 1000) ≤
    (0.008338901232 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13140) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.629839047256 : ℝ) ≤ √(13140 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13140)
  have hdiv : K / √(13140 : ℝ) ≤ K / 114.629839047256 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.629839047256 ≤ (0.008338901232 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13140.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13140 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13140 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13140 := gPlus_lower 13140
end BstLean.Part269.N13140

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13140
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035199342175 : ℝ) ≤ wn 13140 := by
  have hn : √(13140 : ℝ) ≤ 114.629839047257 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13140 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.629839047257 ≤ 2 / √(13140 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243303162 : ℝ) ≤ rhoBar 13140 BstLean.Part154.csC ∧
    rhoBar 13140 BstLean.Part154.csC ≤ 0.000243303539 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035199342175 : ℝ) / (1.295212 * 13140) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035199342176 : ℝ) / (1.29521 * 13140) := by gcongr
      _ ≤ (0.000243303539 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13140 BstLean.Part154.csC) ≤ 0.000973273353 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13140 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) ≤ 0.000185836590 ∧
    cc1 (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) ≤ 0.000118249117 ∧
    cc2 (rhoBar 13140 BstLean.Part154.csC) ≤ 0.000068644592 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13140 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13140 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13140 BstLean.Part154.csC * nuR (rhoBar 13140 BstLean.Part154.csC)) ≤ 0.000486621878 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243303539 : ℝ) * 0.000973273353 := by gcongr
      _ ≤ (0.000486621878 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13140 BstLean.Part154.csC) * nuR (rhoBar 13140 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973273353 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13140 BstLean.Part154.csC) * rhoBar 13140 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243303539 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243303539 / 2 + 0.399 * 0.000973273353 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185836590 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486621878 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118249117 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243303539 / 1.414213562 := by gcongr
      _ ≤ (0.000068644592 : ℝ) := by norm_num

end BstLean.Part269.N13140

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13140
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) ≤ 1.49142E-7 := by
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13140 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13140 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13140 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185836590 : ℝ) ^ 2 + 0.000118249117 ^ 2 + 3 * 0.000068644592 ^ 2 +
        2 * 0.797885 * 0.000185836590 * 0.000118249117 + 2 * 0.000185836590 * 0.000068644592 +
        4 * 0.797885 * 0.000118249117 * 0.000068644592 := by gcongr
    _ ≤ (1.49142E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13140 BstLean.Part154.csC Θ ≤ 0.002538260482 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13140 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13140 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13140 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035199342176 * 1.49142E-7 / (0.000243303162 : ℝ) := by gcongr
    _ ≤ 0.002538260482 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13140 BstLean.Part154.csC Θ ≤ 0.002814665693 + 0.000641375872 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13140 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13140 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035199342176 : ℝ) * ((2 * Θ * 0.000243303539 +
        (6863 / 10000) * 0.000243303539 * 13140 * 0.000973273353) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002814665693 + 0.000641375872 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13140 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13140 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13140 0.011 Θ ∧ gammaRatio 13140 0.011 Θ ≤ 0.000083641465 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13140 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035199342176 : ℝ) * 0.525 / ((1 - 0.011) * 13140) := by gcongr
      _ ≤ (0.000083641465 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13140 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13140 0.011 Θ) :=
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
    badAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13140 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13140 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13140 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13140 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13140 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13140 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13140 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13140 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13140 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13140 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035199342176 : ℝ) * 13140 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003163754179 + 0.003179636354 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13140

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13140
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13140 BstLean.Part154.csC) (piBar (rhoBar 13140 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13140 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13140 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13140 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13140 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13140 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13140 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13140 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13140 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13140 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13140 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051588650617 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13140) ≤ 0.010418208653 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13140 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035199342176)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010418208653 + 2 * 0.737676 / 13140) := by gcongr
    _ ≤ (0.051588650617 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13140 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13140

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13140
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522800098 : ℝ) ≤ plow 13140 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13140) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339663265)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332586754) : eMP 13140 0.011 xi bn ≤ 0.001147812339 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13140 : ℝ) * (1 - 0.011))) ≤ 0.000567579732 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332586754 / (13140 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567579732 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567579732 : ℝ) + 3.141593 * 0.052339663265 / (13140 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147812339 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339663265)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332586754) : PiBarMP 13140 12 0.011 xi bn ≤ 0.158501780777 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13140 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036504612778 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.997631554344 : ℝ) ≤ √((13140 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.629839047256 : ℝ) ≤ √(13140 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13140) ≤ 0.121542596401 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036504612778 + 0.052339663265 * 1.772454 / (2 * (113.997631554344 : ℝ))) * (1 + 0.001147812339) +
        8 / (13140 * 114.629839047256) + 0.121542596401 := by gcongr
    _ ≤ (0.158501780777 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339663265)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332586754) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280367284377) :
    parallelOracle 13140 0.011 xi bn cd ≤ 0.159459286423 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13140 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13140 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522800098 : ℝ) ≤ plow 13140 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.629839047256 : ℝ) ≤ √(13140 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280367284377 : ℝ) / (2 * 0.560522800098 * 114.629839047256)) * 0.158501780777 +
        0.280367284377 ^ 2 / (2 * 0.560522800098 * 114.629839047256) := by gcongr
    _ ≤ (0.159459286423 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339663265) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332586754)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280367284377) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13140 13140 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522800098 : ℝ) ≤ plow 13140 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.629839047256 : ℝ) ≤ √(13140 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13140 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13140 Θ 1.22 ≤ 0.011568545425 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.629839047256 := by gcongr <;> linarith
      _ ≤ (0.011568545425 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13140 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13140 13140 0.011 ≤ 0.008338901232 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13140 13140 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13140 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13140 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13140 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13140 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159459286423 + 0.011568545425 + (0.008338901232 : ℝ) *
        (1 + 2 * (0.280367284377 + 0.011568545425) / (0.560522800098 * 114.629839047256))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13140]

end BstLean.Part269.N13140

/-! The original eight local profiles supply actual 13140 moment certificates. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13140 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052339663265 ∧
    0 ≤ bN 13140 BstLean.Part154.csC (groupTheta g) ∧ bN 13140 BstLean.Part154.csC (groupTheta g) ≤ 0.001332586754 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13140 13140 0.011
      (momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13140 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13140 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13140 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228778633760 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13140 0.011
      (momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13140 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13140
/-! The actual computed-centre upper energy formula at 13140. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13140

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13140)
open BstLean.Part268 (cell13140)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084301096239
  | 2 => 0.085225194464
  | 3 => 0.086144828931
  | 4 => 0.087060804875
  | 5 => 0.087974113638
  | 6 => 0.088885962419
  | 7 => 0.089797807228
  | 8 => 0.090711389172
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13140 13140 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13140 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13140

/-! Actual upper energy certificates on all 43 source endpoints at 13140. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13140)
open BstLean.Part268 (cell13140)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13140 (gMinus 13140) (1 - (cell13140 i).lower) ≤ 1 ∧
    energyUpper 13140 (gMinus 13140) (BstLean.Part211.gPlus 13140)
      (finiteEnergy 13140 13140 0.011) (1 - (cell13140 i).lower) ≤
      (cell13140 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨10,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨11,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨12,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨13,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨14,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨15,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨16,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨17,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨18,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨19,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨20,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨21,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨22,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨23,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨24,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨25,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨26,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨27,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨28,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨29,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨30,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨31,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨32,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨33,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨34,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨35,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨36,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨37,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨38,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨39,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨40,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨41,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨42,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨43,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨44,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨45,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨46,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨47,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨48,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨49,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨50,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨51,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13140) (by norm_num)
        (q := 1 - (cell13140 ⟨52,by decide⟩).lower)
        (by norm_num [cell13140]) (by norm_num [cell13140])
      exact ⟨E.1,E.2.trans (by norm_num [cell13140])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13140

/-! Source-cell containment and simple scalar guards at 13140. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13140)
open BstLean.Part268 (cell13140)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13140 ⟨10,by decide⟩).lower ∧ (cell13140 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13140 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13140 ⟨11,by decide⟩).lower ∧ (cell13140 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13140 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13140 ⟨12,by decide⟩).lower ∧ (cell13140 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13140 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13140 ⟨13,by decide⟩).lower ∧ (cell13140 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13140 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13140 ⟨14,by decide⟩).lower ∧ (cell13140 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13140 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13140 ⟨15,by decide⟩).lower ∧ (cell13140 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13140 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13140 ⟨16,by decide⟩).lower ∧ (cell13140 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13140 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13140 ⟨17,by decide⟩).lower ∧ (cell13140 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13140 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13140 ⟨18,by decide⟩).lower ∧ (cell13140 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13140 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13140 ⟨19,by decide⟩).lower ∧ (cell13140 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13140 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13140 ⟨20,by decide⟩).lower ∧ (cell13140 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13140 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13140 ⟨21,by decide⟩).lower ∧ (cell13140 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13140 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13140 ⟨22,by decide⟩).lower ∧ (cell13140 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13140 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13140 ⟨23,by decide⟩).lower ∧ (cell13140 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13140 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13140 ⟨24,by decide⟩).lower ∧ (cell13140 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13140 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13140 ⟨25,by decide⟩).lower ∧ (cell13140 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13140 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13140 ⟨26,by decide⟩).lower ∧ (cell13140 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13140 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13140 ⟨27,by decide⟩).lower ∧ (cell13140 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13140 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13140 ⟨28,by decide⟩).lower ∧ (cell13140 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13140 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13140 ⟨29,by decide⟩).lower ∧ (cell13140 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13140 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13140 ⟨30,by decide⟩).lower ∧ (cell13140 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13140 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13140 ⟨31,by decide⟩).lower ∧ (cell13140 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13140 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13140 ⟨32,by decide⟩).lower ∧ (cell13140 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13140 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13140 ⟨33,by decide⟩).lower ∧ (cell13140 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13140 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13140 ⟨34,by decide⟩).lower ∧ (cell13140 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13140 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13140 ⟨35,by decide⟩).lower ∧ (cell13140 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13140 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13140 ⟨36,by decide⟩).lower ∧ (cell13140 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13140 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13140 ⟨37,by decide⟩).lower ∧ (cell13140 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13140 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13140 ⟨38,by decide⟩).lower ∧ (cell13140 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13140 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13140 ⟨39,by decide⟩).lower ∧ (cell13140 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13140 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13140 ⟨40,by decide⟩).lower ∧ (cell13140 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13140 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13140 ⟨41,by decide⟩).lower ∧ (cell13140 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13140 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13140 ⟨42,by decide⟩).lower ∧ (cell13140 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13140 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13140 ⟨43,by decide⟩).lower ∧ (cell13140 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13140 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13140 ⟨44,by decide⟩).lower ∧ (cell13140 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13140 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13140 ⟨45,by decide⟩).lower ∧ (cell13140 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13140 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13140 ⟨46,by decide⟩).lower ∧ (cell13140 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13140 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13140 ⟨47,by decide⟩).lower ∧ (cell13140 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13140 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13140 ⟨48,by decide⟩).lower ∧ (cell13140 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13140 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13140 ⟨49,by decide⟩).lower ∧ (cell13140 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13140 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13140 ⟨50,by decide⟩).lower ∧ (cell13140 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13140 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13140 ⟨51,by decide⟩).lower ∧ (cell13140 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13140 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13140 ⟨52,by decide⟩).lower ∧ (cell13140 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13140 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13140 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13140 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13140,cell13140,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13140 i).lower ∧
    (cell13140 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13140 i).upper ≤ (0.532 : ℝ) ∧
    (cell13140 i).centre ≤ (0.1 : ℝ) ∧ (cell13140 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13140 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13140 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13140

/-! The local source numeric instances at 13140 have no network premises. -/
namespace BstLean.Part269.N13140
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13140)
open BstLean.Part268 (cell13140)

noncomputable def sourceNumerics13140 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13140 (cell13140 i)
      scalarRow13140.M scalarRow13140.H scalarRow13140.xi := by
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
    energy_allowance := scalarRow13140.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13140]
    centre_nonneg := (scalarRow13140.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13140])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13140
/-! Actual 13141 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13141 ≤ (1.035197991274 : ℝ) := by
  have hr : (114.634200830293 : ℝ) ≤ √(13141 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.634200830293 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13141 13141 (11 / 1000) ≤
    (0.008338583938 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13141) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.634200830293 : ℝ) ≤ √(13141 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13141)
  have hdiv : K / √(13141 : ℝ) ≤ K / 114.634200830293 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.634200830293 ≤ (0.008338583938 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13141.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13141 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13141 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13141 := gPlus_lower 13141
end BstLean.Part269.N13141

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13141
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035197991273 : ℝ) ≤ wn 13141 := by
  have hn : √(13141 : ℝ) ≤ 114.634200830294 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13141 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.634200830294 ≤ 2 / √(13141 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243284330 : ℝ) ≤ rhoBar 13141 BstLean.Part154.csC ∧
    rhoBar 13141 BstLean.Part154.csC ≤ 0.000243284706 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035197991273 : ℝ) / (1.295212 * 13141) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035197991274 : ℝ) / (1.29521 * 13141) := by gcongr
      _ ≤ (0.000243284706 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13141 BstLean.Part154.csC) ≤ 0.000973198012 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13141 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) ≤ 0.000185822205 ∧
    cc1 (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) ≤ 0.000118239963 ∧
    cc2 (rhoBar 13141 BstLean.Part154.csC) ≤ 0.000068639278 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13141 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13141 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13141 BstLean.Part154.csC * nuR (rhoBar 13141 BstLean.Part154.csC)) ≤ 0.000486584209 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243284706 : ℝ) * 0.000973198012 := by gcongr
      _ ≤ (0.000486584209 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13141 BstLean.Part154.csC) * nuR (rhoBar 13141 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973198012 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13141 BstLean.Part154.csC) * rhoBar 13141 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243284706 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243284706 / 2 + 0.399 * 0.000973198012 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185822205 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486584209 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118239963 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243284706 / 1.414213562 := by gcongr
      _ ≤ (0.000068639278 : ℝ) := by norm_num

end BstLean.Part269.N13141

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13141
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) ≤ 1.49118E-7 := by
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13141 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13141 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13141 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185822205 : ℝ) ^ 2 + 0.000118239963 ^ 2 + 3 * 0.000068639278 ^ 2 +
        2 * 0.797885 * 0.000185822205 * 0.000118239963 + 2 * 0.000185822205 * 0.000068639278 +
        4 * 0.797885 * 0.000118239963 * 0.000068639278 := by gcongr
    _ ≤ (1.49118E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13141 BstLean.Part154.csC Θ ≤ 0.002538045160 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13141 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13141 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13141 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035197991274 * 1.49118E-7 / (0.000243284330 : ℝ) := by gcongr
    _ ≤ 0.002538045160 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13141 BstLean.Part154.csC Θ ≤ 0.002814440457 + 0.000641325390 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13141 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13141 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035197991274 : ℝ) * ((2 * Θ * 0.000243284706 +
        (6863 / 10000) * 0.000243284706 * 13141 * 0.000973198012) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002814440457 + 0.000641325390 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13141 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13141 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13141 0.011 Θ ∧ gammaRatio 13141 0.011 Θ ≤ 0.000083634991 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13141 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035197991274 : ℝ) * 0.525 / ((1 - 0.011) * 13141) := by gcongr
      _ ≤ (0.000083634991 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13141 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13141 0.011 Θ) :=
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
    badAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13141 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13141 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13141 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13141 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13141 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13141 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13141 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13141 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13141 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13141 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035197991274 : ℝ) * 13141 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003163528943 + 0.003179370550 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13141

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13141
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13141 BstLean.Part154.csC) (piBar (rhoBar 13141 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13141 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13141 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13141 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13141 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13141 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13141 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13141 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13141 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13141 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13141 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051586666765 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13141) ≤ 0.010417812245 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13141 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035197991274)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010417812245 + 2 * 0.737676 / 13141) := by gcongr
    _ ≤ (0.051586666765 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13141 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13141

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13141
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522842340 : ℝ) ≤ plow 13141 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13141) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339298482)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332473709) : eMP 13141 0.011 xi bn ≤ 0.001147719948 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13141 : ℝ) * (1 - 0.011))) ≤ 0.000567534062 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332473709 / (13141 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567534062 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567534062 : ℝ) + 3.141593 * 0.052339298482 / (13141 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147719948 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339298482)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332473709) : PiBarMP 13141 12 0.011 xi bn ≤ 0.158495583601 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13141 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036503064379 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.001969281236 : ℝ) ≤ √((13141 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.634200830293 : ℝ) ≤ √(13141 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13141) ≤ 0.121537971756 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036503064379 + 0.052339298482 * 1.772454 / (2 * (114.001969281236 : ℝ))) * (1 + 0.001147719948) +
        8 / (13141 * 114.634200830293) + 0.121537971756 := by gcongr
    _ ≤ (0.158495583601 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339298482)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332473709) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280364503284) :
    parallelOracle 13141 0.011 xi bn cd ≤ 0.159453023658 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13141 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13141 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522842340 : ℝ) ≤ plow 13141 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.634200830293 : ℝ) ≤ √(13141 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280364503284 : ℝ) / (2 * 0.560522842340 * 114.634200830293)) * 0.158495583601 +
        0.280364503284 ^ 2 / (2 * 0.560522842340 * 114.634200830293) := by gcongr
    _ ≤ (0.159453023658 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052339298482) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332473709)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280364503284) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13141 13141 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522842340 : ℝ) ≤ plow 13141 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.634200830293 : ℝ) ≤ √(13141 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13141 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13141 Θ 1.22 ≤ 0.011568105247 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.634200830293 := by gcongr <;> linarith
      _ ≤ (0.011568105247 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13141 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13141 13141 0.011 ≤ 0.008338583938 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13141 13141 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13141 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13141 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13141 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13141 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159453023658 + 0.011568105247 + (0.008338583938 : ℝ) *
        (1 + 2 * (0.280364503284 + 0.011568105247) / (0.560522842340 * 114.634200830293))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13141]

end BstLean.Part269.N13141

/-! The original eight local profiles supply actual 13141 moment certificates. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13141 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052339298482 ∧
    0 ≤ bN 13141 BstLean.Part154.csC (groupTheta g) ∧ bN 13141 BstLean.Part154.csC (groupTheta g) ≤ 0.001332473709 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13141 13141 0.011
      (momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13141 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13141 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13141 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228777836519 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13141 0.011
      (momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13141 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13141
/-! The actual computed-centre upper energy formula at 13141. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13141

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13141)
open BstLean.Part268 (cell13141)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084298584139
  | 2 => 0.085222651470
  | 3 => 0.086142250667
  | 4 => 0.087058185921
  | 5 => 0.087971447332
  | 6 => 0.088883240637
  | 7 => 0.089795020135
  | 8 => 0.090708524939
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13141 13141 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13141 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13141

/-! Actual upper energy certificates on all 43 source endpoints at 13141. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13141)
open BstLean.Part268 (cell13141)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13141 (gMinus 13141) (1 - (cell13141 i).lower) ≤ 1 ∧
    energyUpper 13141 (gMinus 13141) (BstLean.Part211.gPlus 13141)
      (finiteEnergy 13141 13141 0.011) (1 - (cell13141 i).lower) ≤
      (cell13141 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨10,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨11,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨12,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨13,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨14,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨15,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨16,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨17,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨18,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨19,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨20,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨21,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨22,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨23,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨24,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨25,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨26,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨27,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨28,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨29,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨30,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨31,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨32,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨33,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨34,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨35,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨36,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨37,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨38,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨39,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨40,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨41,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨42,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨43,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨44,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨45,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨46,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨47,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨48,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨49,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨50,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨51,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13141) (by norm_num)
        (q := 1 - (cell13141 ⟨52,by decide⟩).lower)
        (by norm_num [cell13141]) (by norm_num [cell13141])
      exact ⟨E.1,E.2.trans (by norm_num [cell13141])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13141

/-! Source-cell containment and simple scalar guards at 13141. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13141)
open BstLean.Part268 (cell13141)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13141 ⟨10,by decide⟩).lower ∧ (cell13141 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13141 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13141 ⟨11,by decide⟩).lower ∧ (cell13141 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13141 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13141 ⟨12,by decide⟩).lower ∧ (cell13141 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13141 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13141 ⟨13,by decide⟩).lower ∧ (cell13141 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13141 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13141 ⟨14,by decide⟩).lower ∧ (cell13141 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13141 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13141 ⟨15,by decide⟩).lower ∧ (cell13141 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13141 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13141 ⟨16,by decide⟩).lower ∧ (cell13141 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13141 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13141 ⟨17,by decide⟩).lower ∧ (cell13141 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13141 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13141 ⟨18,by decide⟩).lower ∧ (cell13141 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13141 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13141 ⟨19,by decide⟩).lower ∧ (cell13141 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13141 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13141 ⟨20,by decide⟩).lower ∧ (cell13141 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13141 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13141 ⟨21,by decide⟩).lower ∧ (cell13141 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13141 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13141 ⟨22,by decide⟩).lower ∧ (cell13141 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13141 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13141 ⟨23,by decide⟩).lower ∧ (cell13141 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13141 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13141 ⟨24,by decide⟩).lower ∧ (cell13141 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13141 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13141 ⟨25,by decide⟩).lower ∧ (cell13141 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13141 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13141 ⟨26,by decide⟩).lower ∧ (cell13141 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13141 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13141 ⟨27,by decide⟩).lower ∧ (cell13141 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13141 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13141 ⟨28,by decide⟩).lower ∧ (cell13141 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13141 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13141 ⟨29,by decide⟩).lower ∧ (cell13141 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13141 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13141 ⟨30,by decide⟩).lower ∧ (cell13141 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13141 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13141 ⟨31,by decide⟩).lower ∧ (cell13141 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13141 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13141 ⟨32,by decide⟩).lower ∧ (cell13141 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13141 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13141 ⟨33,by decide⟩).lower ∧ (cell13141 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13141 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13141 ⟨34,by decide⟩).lower ∧ (cell13141 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13141 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13141 ⟨35,by decide⟩).lower ∧ (cell13141 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13141 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13141 ⟨36,by decide⟩).lower ∧ (cell13141 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13141 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13141 ⟨37,by decide⟩).lower ∧ (cell13141 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13141 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13141 ⟨38,by decide⟩).lower ∧ (cell13141 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13141 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13141 ⟨39,by decide⟩).lower ∧ (cell13141 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13141 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13141 ⟨40,by decide⟩).lower ∧ (cell13141 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13141 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13141 ⟨41,by decide⟩).lower ∧ (cell13141 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13141 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13141 ⟨42,by decide⟩).lower ∧ (cell13141 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13141 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13141 ⟨43,by decide⟩).lower ∧ (cell13141 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13141 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13141 ⟨44,by decide⟩).lower ∧ (cell13141 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13141 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13141 ⟨45,by decide⟩).lower ∧ (cell13141 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13141 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13141 ⟨46,by decide⟩).lower ∧ (cell13141 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13141 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13141 ⟨47,by decide⟩).lower ∧ (cell13141 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13141 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13141 ⟨48,by decide⟩).lower ∧ (cell13141 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13141 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13141 ⟨49,by decide⟩).lower ∧ (cell13141 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13141 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13141 ⟨50,by decide⟩).lower ∧ (cell13141 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13141 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13141 ⟨51,by decide⟩).lower ∧ (cell13141 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13141 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13141 ⟨52,by decide⟩).lower ∧ (cell13141 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13141 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13141 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13141 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13141,cell13141,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13141 i).lower ∧
    (cell13141 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13141 i).upper ≤ (0.532 : ℝ) ∧
    (cell13141 i).centre ≤ (0.1 : ℝ) ∧ (cell13141 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13141 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13141 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13141

/-! The local source numeric instances at 13141 have no network premises. -/
namespace BstLean.Part269.N13141
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13141)
open BstLean.Part268 (cell13141)

noncomputable def sourceNumerics13141 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13141 (cell13141 i)
      scalarRow13141.M scalarRow13141.H scalarRow13141.xi := by
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
    energy_allowance := scalarRow13141.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13141]
    centre_nonneg := (scalarRow13141.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13141])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13141
/-! Actual 13142 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13142 ≤ (1.035196640526 : ℝ) := by
  have hr : (114.638562447371 : ℝ) ≤ √(13142 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.638562447371 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13142 13142 (11 / 1000) ≤
    (0.008338266680 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13142) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.638562447371 : ℝ) ≤ √(13142 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13142)
  have hdiv : K / √(13142 : ℝ) ≤ K / 114.638562447371 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.638562447371 ≤ (0.008338266680 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13142.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13142 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13142 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13142 := gPlus_lower 13142
end BstLean.Part269.N13142

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13142
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035196640525 : ℝ) ≤ wn 13142 := by
  have hn : √(13142 : ℝ) ≤ 114.638562447372 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13142 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.638562447372 ≤ 2 / √(13142 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243265500 : ℝ) ≤ rhoBar 13142 BstLean.Part154.csC ∧
    rhoBar 13142 BstLean.Part154.csC ≤ 0.000243265877 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035196640525 : ℝ) / (1.295212 * 13142) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035196640526 : ℝ) / (1.29521 * 13142) := by gcongr
      _ ≤ (0.000243265877 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13142 BstLean.Part154.csC) ≤ 0.000973122687 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13142 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) ≤ 0.000185807822 ∧
    cc1 (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) ≤ 0.000118230812 ∧
    cc2 (rhoBar 13142 BstLean.Part154.csC) ≤ 0.000068633966 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13142 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13142 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13142 BstLean.Part154.csC * nuR (rhoBar 13142 BstLean.Part154.csC)) ≤ 0.000486546549 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243265877 : ℝ) * 0.000973122687 := by gcongr
      _ ≤ (0.000486546549 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13142 BstLean.Part154.csC) * nuR (rhoBar 13142 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973122687 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13142 BstLean.Part154.csC) * rhoBar 13142 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243265877 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243265877 / 2 + 0.399 * 0.000973122687 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185807822 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486546549 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118230812 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243265877 / 1.414213562 := by gcongr
      _ ≤ (0.000068633966 : ℝ) := by norm_num

end BstLean.Part269.N13142

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13142
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) ≤ 1.49095E-7 := by
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13142 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13142 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13142 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185807822 : ℝ) ^ 2 + 0.000118230812 ^ 2 + 3 * 0.000068633966 ^ 2 +
        2 * 0.797885 * 0.000185807822 * 0.000118230812 + 2 * 0.000185807822 * 0.000068633966 +
        4 * 0.797885 * 0.000118230812 * 0.000068633966 := by gcongr
    _ ≤ (1.49095E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13142 BstLean.Part154.csC Θ ≤ 0.002537846808 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13142 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13142 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13142 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035196640526 * 1.49095E-7 / (0.000243265500 : ℝ) := by gcongr
    _ ≤ 0.002537846808 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13142 BstLean.Part154.csC Θ ≤ 0.002814215281 + 0.000641274917 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13142 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13142 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035196640526 : ℝ) * ((2 * Θ * 0.000243265877 +
        (6863 / 10000) * 0.000243265877 * 13142 * 0.000973122687) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002814215281 + 0.000641274917 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13142 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13142 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13142 0.011 Θ ∧ gammaRatio 13142 0.011 Θ ≤ 0.000083628518 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13142 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035196640526 : ℝ) * 0.525 / ((1 - 0.011) * 13142) := by gcongr
      _ ≤ (0.000083628518 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13142 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13142 0.011 Θ) :=
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
    badAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13142 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13142 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13142 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13142 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13142 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13142 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13142 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13142 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13142 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13142 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035196640526 : ℝ) * 13142 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003163303767 + 0.003179121725 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13142

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13142
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13142 BstLean.Part154.csC) (piBar (rhoBar 13142 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13142 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13142 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13142 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13142 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13142 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13142 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13142 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13142 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13142 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13142 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051584683139 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13142) ≤ 0.010417415882 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13142 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035196640526)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010417415882 + 2 * 0.737676 / 13142) := by gcongr
    _ ≤ (0.051584683139 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13142 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13142

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13142
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522884576 : ℝ) ≤ plow 13142 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13142) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338942673)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332369575) : eMP 13142 0.011 xi bn ≤ 0.001147631361 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13142 : ℝ) * (1 - 0.011))) ≤ 0.000567490293 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332369575 / (13142 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567490293 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567490293 : ℝ) + 3.141593 * 0.052338942673 / (13142 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147631361 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338942673)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332369575) : PiBarMP 13142 12 0.011 xi bn ≤ 0.158489509303 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13142 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036501637977 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.006306843086 : ℝ) ≤ √((13142 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.638562447371 : ℝ) ≤ √(13142 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13142) ≤ 0.121533347640 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036501637977 + 0.052338942673 * 1.772454 / (2 * (114.006306843086 : ℝ))) * (1 + 0.001147631361) +
        8 / (13142 * 114.638562447371) + 0.121533347640 := by gcongr
    _ ≤ (0.158489509303 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338942673)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332369575) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280361742027) :
    parallelOracle 13142 0.011 xi bn cd ≤ 0.159446884156 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13142 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13142 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522884576 : ℝ) ≤ plow 13142 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.638562447371 : ℝ) ≤ √(13142 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280361742027 : ℝ) / (2 * 0.560522884576 * 114.638562447371)) * 0.158489509303 +
        0.280361742027 ^ 2 / (2 * 0.560522884576 * 114.638562447371) := by gcongr
    _ ≤ (0.159446884156 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338942673) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332369575)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280361742027) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13142 13142 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522884576 : ℝ) ≤ plow 13142 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.638562447371 : ℝ) ≤ √(13142 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13142 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13142 Θ 1.22 ≤ 0.011567665118 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.638562447371 := by gcongr <;> linarith
      _ ≤ (0.011567665118 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13142 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13142 13142 0.011 ≤ 0.008338266680 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13142 13142 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13142 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13142 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13142 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13142 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159446884156 + 0.011567665118 + (0.008338266680 : ℝ) *
        (1 + 2 * (0.280361742027 + 0.011567665118) / (0.560522884576 * 114.638562447371))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13142]

end BstLean.Part269.N13142

/-! The original eight local profiles supply actual 13142 moment certificates. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13142 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052338942673 ∧
    0 ≤ bN 13142 BstLean.Part154.csC (groupTheta g) ∧ bN 13142 BstLean.Part154.csC (groupTheta g) ≤ 0.001332369575 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13142 13142 0.011
      (momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13142 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13142 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13142 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228777058888 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13142 0.011
      (momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13142 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13142
/-! The actual computed-centre upper energy formula at 13142. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13142

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13142)
open BstLean.Part268 (cell13142)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084296072751
  | 2 => 0.085220109211
  | 3 => 0.086139673168
  | 4 => 0.087055567768
  | 5 => 0.087968781872
  | 6 => 0.088880519755
  | 7 => 0.089792234008
  | 8 => 0.090705661755
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13142 13142 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13142 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13142

/-! Actual upper energy certificates on all 43 source endpoints at 13142. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13142)
open BstLean.Part268 (cell13142)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13142 (gMinus 13142) (1 - (cell13142 i).lower) ≤ 1 ∧
    energyUpper 13142 (gMinus 13142) (BstLean.Part211.gPlus 13142)
      (finiteEnergy 13142 13142 0.011) (1 - (cell13142 i).lower) ≤
      (cell13142 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨10,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨11,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨12,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨13,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨14,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨15,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨16,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨17,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨18,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨19,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨20,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨21,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨22,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨23,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨24,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨25,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨26,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨27,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨28,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨29,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨30,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨31,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨32,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨33,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨34,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨35,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨36,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨37,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨38,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨39,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨40,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨41,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨42,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨43,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨44,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨45,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨46,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨47,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨48,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨49,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨50,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨51,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13142) (by norm_num)
        (q := 1 - (cell13142 ⟨52,by decide⟩).lower)
        (by norm_num [cell13142]) (by norm_num [cell13142])
      exact ⟨E.1,E.2.trans (by norm_num [cell13142])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13142

/-! Source-cell containment and simple scalar guards at 13142. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13142)
open BstLean.Part268 (cell13142)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13142 ⟨10,by decide⟩).lower ∧ (cell13142 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13142 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13142 ⟨11,by decide⟩).lower ∧ (cell13142 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13142 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13142 ⟨12,by decide⟩).lower ∧ (cell13142 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13142 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13142 ⟨13,by decide⟩).lower ∧ (cell13142 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13142 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13142 ⟨14,by decide⟩).lower ∧ (cell13142 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13142 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13142 ⟨15,by decide⟩).lower ∧ (cell13142 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13142 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13142 ⟨16,by decide⟩).lower ∧ (cell13142 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13142 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13142 ⟨17,by decide⟩).lower ∧ (cell13142 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13142 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13142 ⟨18,by decide⟩).lower ∧ (cell13142 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13142 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13142 ⟨19,by decide⟩).lower ∧ (cell13142 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13142 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13142 ⟨20,by decide⟩).lower ∧ (cell13142 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13142 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13142 ⟨21,by decide⟩).lower ∧ (cell13142 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13142 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13142 ⟨22,by decide⟩).lower ∧ (cell13142 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13142 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13142 ⟨23,by decide⟩).lower ∧ (cell13142 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13142 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13142 ⟨24,by decide⟩).lower ∧ (cell13142 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13142 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13142 ⟨25,by decide⟩).lower ∧ (cell13142 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13142 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13142 ⟨26,by decide⟩).lower ∧ (cell13142 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13142 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13142 ⟨27,by decide⟩).lower ∧ (cell13142 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13142 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13142 ⟨28,by decide⟩).lower ∧ (cell13142 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13142 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13142 ⟨29,by decide⟩).lower ∧ (cell13142 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13142 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13142 ⟨30,by decide⟩).lower ∧ (cell13142 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13142 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13142 ⟨31,by decide⟩).lower ∧ (cell13142 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13142 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13142 ⟨32,by decide⟩).lower ∧ (cell13142 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13142 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13142 ⟨33,by decide⟩).lower ∧ (cell13142 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13142 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13142 ⟨34,by decide⟩).lower ∧ (cell13142 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13142 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13142 ⟨35,by decide⟩).lower ∧ (cell13142 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13142 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13142 ⟨36,by decide⟩).lower ∧ (cell13142 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13142 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13142 ⟨37,by decide⟩).lower ∧ (cell13142 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13142 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13142 ⟨38,by decide⟩).lower ∧ (cell13142 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13142 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13142 ⟨39,by decide⟩).lower ∧ (cell13142 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13142 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13142 ⟨40,by decide⟩).lower ∧ (cell13142 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13142 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13142 ⟨41,by decide⟩).lower ∧ (cell13142 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13142 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13142 ⟨42,by decide⟩).lower ∧ (cell13142 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13142 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13142 ⟨43,by decide⟩).lower ∧ (cell13142 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13142 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13142 ⟨44,by decide⟩).lower ∧ (cell13142 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13142 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13142 ⟨45,by decide⟩).lower ∧ (cell13142 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13142 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13142 ⟨46,by decide⟩).lower ∧ (cell13142 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13142 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13142 ⟨47,by decide⟩).lower ∧ (cell13142 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13142 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13142 ⟨48,by decide⟩).lower ∧ (cell13142 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13142 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13142 ⟨49,by decide⟩).lower ∧ (cell13142 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13142 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13142 ⟨50,by decide⟩).lower ∧ (cell13142 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13142 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13142 ⟨51,by decide⟩).lower ∧ (cell13142 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13142 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13142 ⟨52,by decide⟩).lower ∧ (cell13142 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13142 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13142 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13142 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13142,cell13142,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13142 i).lower ∧
    (cell13142 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13142 i).upper ≤ (0.532 : ℝ) ∧
    (cell13142 i).centre ≤ (0.1 : ℝ) ∧ (cell13142 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13142 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13142 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13142

/-! The local source numeric instances at 13142 have no network premises. -/
namespace BstLean.Part269.N13142
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13142)
open BstLean.Part268 (cell13142)

noncomputable def sourceNumerics13142 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13142 (cell13142 i)
      scalarRow13142.M scalarRow13142.H scalarRow13142.xi := by
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
    energy_allowance := scalarRow13142.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13142]
    centre_nonneg := (scalarRow13142.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13142])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13142
/-! Actual 13143 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13143 ≤ (1.035195289934 : ℝ) := by
  have hr : (114.642923898511 : ℝ) ≤ √(13143 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.642923898511 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13143 13143 (11 / 1000) ≤
    (0.008337949459 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13143) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.642923898511 : ℝ) ≤ √(13143 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13143)
  have hdiv : K / √(13143 : ℝ) ≤ K / 114.642923898511 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.642923898511 ≤ (0.008337949459 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13143.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13143 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13143 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13143 := gPlus_lower 13143
end BstLean.Part269.N13143

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13143
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035195289933 : ℝ) ≤ wn 13143 := by
  have hn : √(13143 : ℝ) ≤ 114.642923898512 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13143 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.642923898512 ≤ 2 / √(13143 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243246674 : ℝ) ≤ rhoBar 13143 BstLean.Part154.csC ∧
    rhoBar 13143 BstLean.Part154.csC ≤ 0.000243247050 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035195289933 : ℝ) / (1.295212 * 13143) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035195289934 : ℝ) / (1.29521 * 13143) := by gcongr
      _ ≤ (0.000243247050 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13143 BstLean.Part154.csC) ≤ 0.000973047370 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13143 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) ≤ 0.000185793442 ∧
    cc1 (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) ≤ 0.000118221661 ∧
    cc2 (rhoBar 13143 BstLean.Part154.csC) ≤ 0.000068628654 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13143 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13143 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13143 BstLean.Part154.csC * nuR (rhoBar 13143 BstLean.Part154.csC)) ≤ 0.000486508893 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243247050 : ℝ) * 0.000973047370 := by gcongr
      _ ≤ (0.000486508893 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13143 BstLean.Part154.csC) * nuR (rhoBar 13143 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973047370 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13143 BstLean.Part154.csC) * rhoBar 13143 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243247050 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243247050 / 2 + 0.399 * 0.000973047370 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185793442 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486508893 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118221661 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243247050 / 1.414213562 := by gcongr
      _ ≤ (0.000068628654 : ℝ) := by norm_num

end BstLean.Part269.N13143

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13143
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) ≤ 1.49072E-7 := by
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13143 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13143 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13143 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185793442 : ℝ) ^ 2 + 0.000118221661 ^ 2 + 3 * 0.000068628654 ^ 2 +
        2 * 0.797885 * 0.000185793442 * 0.000118221661 + 2 * 0.000185793442 * 0.000068628654 +
        4 * 0.797885 * 0.000118221661 * 0.000068628654 := by gcongr
    _ ≤ (1.49072E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13143 BstLean.Part154.csC Θ ≤ 0.002537648384 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13143 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13143 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13143 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035195289934 * 1.49072E-7 / (0.000243246674 : ℝ) := by gcongr
    _ ≤ 0.002537648384 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13143 BstLean.Part154.csC Θ ≤ 0.002813990120 + 0.000641224451 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13143 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13143 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035195289934 : ℝ) * ((2 * Θ * 0.000243247050 +
        (6863 / 10000) * 0.000243247050 * 13143 * 0.000973047370) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002813990120 + 0.000641224451 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13143 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13143 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13143 0.011 Θ ∧ gammaRatio 13143 0.011 Θ ≤ 0.000083622046 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13143 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035195289934 : ℝ) * 0.525 / ((1 - 0.011) * 13143) := by gcongr
      _ ≤ (0.000083622046 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13143 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13143 0.011 Θ) :=
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
    badAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13143 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13143 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13143 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13143 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13143 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13143 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13143 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13143 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13143 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13143 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035195289934 : ℝ) * 13143 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003163078606 + 0.003178872835 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13143

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13143
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13143 BstLean.Part154.csC) (piBar (rhoBar 13143 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13143 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13143 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13143 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13143 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13143 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13143 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13143 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13143 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13143 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13143 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051582699740 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13143) ≤ 0.010417019564 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13143 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035195289934)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010417019564 + 2 * 0.737676 / 13143) := by gcongr
    _ ≤ (0.051582699740 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13143 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13143

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13143
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522926805 : ℝ) ≤ plow 13143 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13143) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338586845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332265402) : eMP 13143 0.011 xi bn ≤ 0.001147542762 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13143 : ℝ) * (1 - 0.011))) ≤ 0.000567446518 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332265402 / (13143 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567446518 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567446518 : ℝ) + 3.141593 * 0.052338586845 / (13143 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147542762 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338586845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332265402) : PiBarMP 13143 12 0.011 xi bn ≤ 0.158483434944 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13143 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036500210986 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.010644239912 : ℝ) ≤ √((13143 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.642923898511 : ℝ) ≤ √(13143 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13143) ≤ 0.121528724051 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036500210986 + 0.052338586845 * 1.772454 / (2 * (114.010644239912 : ℝ))) * (1 + 0.001147542762) +
        8 / (13143 * 114.642923898511) + 0.121528724051 := by gcongr
    _ ≤ (0.158483434944 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338586845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332265402) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280358980952) :
    parallelOracle 13143 0.011 xi bn cd ≤ 0.159440744600 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13143 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13143 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522926805 : ℝ) ≤ plow 13143 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.642923898511 : ℝ) ≤ √(13143 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280358980952 : ℝ) / (2 * 0.560522926805 * 114.642923898511)) * 0.158483434944 +
        0.280358980952 ^ 2 / (2 * 0.560522926805 * 114.642923898511) := by gcongr
    _ ≤ (0.159440744600 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338586845) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332265402)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280358980952) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13143 13143 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522926805 : ℝ) ≤ plow 13143 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.642923898511 : ℝ) ≤ √(13143 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13143 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13143 Θ 1.22 ≤ 0.011567225041 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.642923898511 := by gcongr <;> linarith
      _ ≤ (0.011567225041 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13143 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13143 13143 0.011 ≤ 0.008337949459 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13143 13143 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13143 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13143 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13143 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13143 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159440744600 + 0.011567225041 + (0.008337949459 : ℝ) *
        (1 + 2 * (0.280358980952 + 0.011567225041) / (0.560522926805 * 114.642923898511))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13143]

end BstLean.Part269.N13143

/-! The original eight local profiles supply actual 13143 moment certificates. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13143 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052338586845 ∧
    0 ≤ bN 13143 BstLean.Part154.csC (groupTheta g) ∧ bN 13143 BstLean.Part154.csC (groupTheta g) ≤ 0.001332265402 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13143 13143 0.011
      (momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13143 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13143 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13143 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228776281212 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13143 0.011
      (momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13143 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13143
/-! The actual computed-centre upper energy formula at 13143. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13143

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13143)
open BstLean.Part268 (cell13143)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084293562073
  | 2 => 0.085217567686
  | 3 => 0.086137096433
  | 4 => 0.087052950415
  | 5 => 0.087966117257
  | 6 => 0.088877799774
  | 7 => 0.089789448849
  | 8 => 0.090702799618
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13143 13143 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13143 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13143

/-! Actual upper energy certificates on all 43 source endpoints at 13143. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13143)
open BstLean.Part268 (cell13143)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13143 (gMinus 13143) (1 - (cell13143 i).lower) ≤ 1 ∧
    energyUpper 13143 (gMinus 13143) (BstLean.Part211.gPlus 13143)
      (finiteEnergy 13143 13143 0.011) (1 - (cell13143 i).lower) ≤
      (cell13143 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨10,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨11,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨12,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨13,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨14,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨15,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨16,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨17,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨18,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨19,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨20,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨21,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨22,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨23,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨24,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨25,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨26,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨27,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨28,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨29,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨30,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨31,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨32,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨33,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨34,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨35,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨36,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨37,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨38,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨39,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨40,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨41,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨42,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨43,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨44,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨45,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨46,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨47,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨48,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨49,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨50,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨51,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13143) (by norm_num)
        (q := 1 - (cell13143 ⟨52,by decide⟩).lower)
        (by norm_num [cell13143]) (by norm_num [cell13143])
      exact ⟨E.1,E.2.trans (by norm_num [cell13143])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13143

/-! Source-cell containment and simple scalar guards at 13143. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13143)
open BstLean.Part268 (cell13143)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13143 ⟨10,by decide⟩).lower ∧ (cell13143 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13143 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13143 ⟨11,by decide⟩).lower ∧ (cell13143 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13143 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13143 ⟨12,by decide⟩).lower ∧ (cell13143 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13143 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13143 ⟨13,by decide⟩).lower ∧ (cell13143 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13143 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13143 ⟨14,by decide⟩).lower ∧ (cell13143 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13143 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13143 ⟨15,by decide⟩).lower ∧ (cell13143 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13143 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13143 ⟨16,by decide⟩).lower ∧ (cell13143 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13143 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13143 ⟨17,by decide⟩).lower ∧ (cell13143 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13143 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13143 ⟨18,by decide⟩).lower ∧ (cell13143 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13143 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13143 ⟨19,by decide⟩).lower ∧ (cell13143 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13143 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13143 ⟨20,by decide⟩).lower ∧ (cell13143 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13143 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13143 ⟨21,by decide⟩).lower ∧ (cell13143 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13143 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13143 ⟨22,by decide⟩).lower ∧ (cell13143 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13143 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13143 ⟨23,by decide⟩).lower ∧ (cell13143 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13143 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13143 ⟨24,by decide⟩).lower ∧ (cell13143 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13143 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13143 ⟨25,by decide⟩).lower ∧ (cell13143 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13143 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13143 ⟨26,by decide⟩).lower ∧ (cell13143 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13143 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13143 ⟨27,by decide⟩).lower ∧ (cell13143 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13143 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13143 ⟨28,by decide⟩).lower ∧ (cell13143 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13143 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13143 ⟨29,by decide⟩).lower ∧ (cell13143 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13143 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13143 ⟨30,by decide⟩).lower ∧ (cell13143 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13143 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13143 ⟨31,by decide⟩).lower ∧ (cell13143 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13143 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13143 ⟨32,by decide⟩).lower ∧ (cell13143 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13143 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13143 ⟨33,by decide⟩).lower ∧ (cell13143 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13143 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13143 ⟨34,by decide⟩).lower ∧ (cell13143 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13143 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13143 ⟨35,by decide⟩).lower ∧ (cell13143 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13143 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13143 ⟨36,by decide⟩).lower ∧ (cell13143 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13143 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13143 ⟨37,by decide⟩).lower ∧ (cell13143 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13143 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13143 ⟨38,by decide⟩).lower ∧ (cell13143 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13143 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13143 ⟨39,by decide⟩).lower ∧ (cell13143 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13143 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13143 ⟨40,by decide⟩).lower ∧ (cell13143 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13143 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13143 ⟨41,by decide⟩).lower ∧ (cell13143 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13143 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13143 ⟨42,by decide⟩).lower ∧ (cell13143 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13143 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13143 ⟨43,by decide⟩).lower ∧ (cell13143 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13143 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13143 ⟨44,by decide⟩).lower ∧ (cell13143 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13143 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13143 ⟨45,by decide⟩).lower ∧ (cell13143 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13143 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13143 ⟨46,by decide⟩).lower ∧ (cell13143 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13143 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13143 ⟨47,by decide⟩).lower ∧ (cell13143 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13143 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13143 ⟨48,by decide⟩).lower ∧ (cell13143 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13143 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13143 ⟨49,by decide⟩).lower ∧ (cell13143 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13143 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13143 ⟨50,by decide⟩).lower ∧ (cell13143 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13143 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13143 ⟨51,by decide⟩).lower ∧ (cell13143 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13143 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13143 ⟨52,by decide⟩).lower ∧ (cell13143 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13143 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13143 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13143 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13143,cell13143,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13143 i).lower ∧
    (cell13143 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13143 i).upper ≤ (0.532 : ℝ) ∧
    (cell13143 i).centre ≤ (0.1 : ℝ) ∧ (cell13143 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13143 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13143 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13143

/-! The local source numeric instances at 13143 have no network premises. -/
namespace BstLean.Part269.N13143
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13143)
open BstLean.Part268 (cell13143)

noncomputable def sourceNumerics13143 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13143 (cell13143 i)
      scalarRow13143.M scalarRow13143.H scalarRow13143.xi := by
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
    energy_allowance := scalarRow13143.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13143]
    centre_nonneg := (scalarRow13143.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13143])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13143
/-! Actual 13144 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13144 ≤ (1.035193939496 : ℝ) := by
  have hr : (114.647285183732 : ℝ) ≤ √(13144 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.647285183732 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13144 13144 (11 / 1000) ≤
    (0.008337632273 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13144) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.647285183732 : ℝ) ≤ √(13144 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13144)
  have hdiv : K / √(13144 : ℝ) ≤ K / 114.647285183732 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.647285183732 ≤ (0.008337632273 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13144.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13144 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13144 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13144 := gPlus_lower 13144
end BstLean.Part269.N13144

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13144
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035193939495 : ℝ) ≤ wn 13144 := by
  have hn : √(13144 : ℝ) ≤ 114.647285183733 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13144 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.647285183733 ≤ 2 / √(13144 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243227850 : ℝ) ≤ rhoBar 13144 BstLean.Part154.csC ∧
    rhoBar 13144 BstLean.Part154.csC ≤ 0.000243228227 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035193939495 : ℝ) / (1.295212 * 13144) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035193939496 : ℝ) / (1.29521 * 13144) := by gcongr
      _ ≤ (0.000243228227 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13144 BstLean.Part154.csC) ≤ 0.000972972068 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13144 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) ≤ 0.000185779064 ∧
    cc1 (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) ≤ 0.000118212513 ∧
    cc2 (rhoBar 13144 BstLean.Part154.csC) ≤ 0.000068623344 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13144 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13144 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13144 BstLean.Part154.csC * nuR (rhoBar 13144 BstLean.Part154.csC)) ≤ 0.000486471244 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243228227 : ℝ) * 0.000972972068 := by gcongr
      _ ≤ (0.000486471244 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13144 BstLean.Part154.csC) * nuR (rhoBar 13144 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972972068 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13144 BstLean.Part154.csC) * rhoBar 13144 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243228227 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243228227 / 2 + 0.399 * 0.000972972068 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185779064 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486471244 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118212513 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243228227 / 1.414213562 := by gcongr
      _ ≤ (0.000068623344 : ℝ) := by norm_num

end BstLean.Part269.N13144

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13144
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) ≤ 1.49049E-7 := by
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13144 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13144 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13144 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185779064 : ℝ) ^ 2 + 0.000118212513 ^ 2 + 3 * 0.000068623344 ^ 2 +
        2 * 0.797885 * 0.000185779064 * 0.000118212513 + 2 * 0.000185779064 * 0.000068623344 +
        4 * 0.797885 * 0.000118212513 * 0.000068623344 := by gcongr
    _ ≤ (1.49049E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13144 BstLean.Part154.csC Θ ≤ 0.002537449910 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13144 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13144 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13144 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035193939496 * 1.49049E-7 / (0.000243227850 : ℝ) := by gcongr
    _ ≤ 0.002537449910 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13144 BstLean.Part154.csC Θ ≤ 0.002813765018 + 0.000641173995 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13144 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13144 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035193939496 : ℝ) * ((2 * Θ * 0.000243228227 +
        (6863 / 10000) * 0.000243228227 * 13144 * 0.000972972068) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002813765018 + 0.000641173995 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13144 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13144 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13144 0.011 Θ ∧ gammaRatio 13144 0.011 Θ ≤ 0.000083615575 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13144 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035193939496 : ℝ) * 0.525 / ((1 - 0.011) * 13144) := by gcongr
      _ ≤ (0.000083615575 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13144 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13144 0.011 Θ) :=
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
    badAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13144 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13144 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13144 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13144 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13144 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13144 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13144 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13144 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13144 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13144 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035193939496 : ℝ) * 13144 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003162853504 + 0.003178623905 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13144

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13144
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13144 BstLean.Part154.csC) (piBar (rhoBar 13144 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13144 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13144 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13144 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13144 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13144 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13144 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13144 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13144 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13144 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13144 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051580716567 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13144) ≤ 0.010416623291 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13144 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035193939496)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010416623291 + 2 * 0.737676 / 13144) := by gcongr
    _ ≤ (0.051580716567 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13144 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13144

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13144
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522969027 : ℝ) ≤ plow 13144 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13144) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338231055)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332161203) : eMP 13144 0.011 xi bn ≤ 0.001147454162 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13144 : ℝ) * (1 - 0.011))) ≤ 0.000567402742 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332161203 / (13144 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567402742 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567402742 : ℝ) + 3.141593 * 0.052338231055 / (13144 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147454162 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338231055)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332161203) : PiBarMP 13144 12 0.011 xi bn ≤ 0.158477360702 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13144 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036498783583 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.014981471734 : ℝ) ≤ √((13144 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.647285183732 : ℝ) ≤ √(13144 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13144) ≤ 0.121524100989 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036498783583 + 0.052338231055 * 1.772454 / (2 * (114.014981471734 : ℝ))) * (1 + 0.001147454162) +
        8 / (13144 * 114.647285183732) + 0.121524100989 := by gcongr
    _ ≤ (0.158477360702 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338231055)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332161203) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280356220184) :
    parallelOracle 13144 0.011 xi bn cd ≤ 0.159434605170 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13144 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13144 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522969027 : ℝ) ≤ plow 13144 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.647285183732 : ℝ) ≤ √(13144 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280356220184 : ℝ) / (2 * 0.560522969027 * 114.647285183732)) * 0.158477360702 +
        0.280356220184 ^ 2 / (2 * 0.560522969027 * 114.647285183732) := by gcongr
    _ ≤ (0.159434605170 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052338231055) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332161203)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280356220184) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13144 13144 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522969027 : ℝ) ≤ plow 13144 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.647285183732 : ℝ) ≤ √(13144 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13144 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13144 Θ 1.22 ≤ 0.011566785013 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.647285183732 := by gcongr <;> linarith
      _ ≤ (0.011566785013 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13144 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13144 13144 0.011 ≤ 0.008337632273 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13144 13144 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13144 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13144 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13144 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13144 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159434605170 + 0.011566785013 + (0.008337632273 : ℝ) *
        (1 + 2 * (0.280356220184 + 0.011566785013) / (0.560522969027 * 114.647285183732))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13144]

end BstLean.Part269.N13144

/-! The original eight local profiles supply actual 13144 moment certificates. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13144 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052338231055 ∧
    0 ≤ bN 13144 BstLean.Part154.csC (groupTheta g) ∧ bN 13144 BstLean.Part154.csC (groupTheta g) ≤ 0.001332161203 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13144 13144 0.011
      (momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13144 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13144 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13144 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228775503617 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13144 0.011
      (momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13144 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13144
/-! The actual computed-centre upper energy formula at 13144. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13144

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13144)
open BstLean.Part268 (cell13144)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084291052105
  | 2 => 0.085215026895
  | 3 => 0.086134520461
  | 4 => 0.087050333862
  | 5 => 0.087963453487
  | 6 => 0.088875080692
  | 7 => 0.089786664655
  | 8 => 0.090699938527
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13144 13144 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13144 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13144

/-! Actual upper energy certificates on all 43 source endpoints at 13144. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13144)
open BstLean.Part268 (cell13144)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13144 (gMinus 13144) (1 - (cell13144 i).lower) ≤ 1 ∧
    energyUpper 13144 (gMinus 13144) (BstLean.Part211.gPlus 13144)
      (finiteEnergy 13144 13144 0.011) (1 - (cell13144 i).lower) ≤
      (cell13144 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨10,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨11,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨12,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨13,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨14,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨15,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨16,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨17,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨18,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨19,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨20,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨21,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨22,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨23,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨24,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨25,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨26,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨27,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨28,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨29,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨30,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨31,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨32,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨33,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨34,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨35,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨36,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨37,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨38,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨39,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨40,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨41,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨42,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨43,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨44,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨45,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨46,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨47,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨48,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨49,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨50,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨51,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13144) (by norm_num)
        (q := 1 - (cell13144 ⟨52,by decide⟩).lower)
        (by norm_num [cell13144]) (by norm_num [cell13144])
      exact ⟨E.1,E.2.trans (by norm_num [cell13144])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13144

/-! Source-cell containment and simple scalar guards at 13144. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13144)
open BstLean.Part268 (cell13144)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13144 ⟨10,by decide⟩).lower ∧ (cell13144 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13144 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13144 ⟨11,by decide⟩).lower ∧ (cell13144 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13144 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13144 ⟨12,by decide⟩).lower ∧ (cell13144 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13144 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13144 ⟨13,by decide⟩).lower ∧ (cell13144 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13144 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13144 ⟨14,by decide⟩).lower ∧ (cell13144 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13144 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13144 ⟨15,by decide⟩).lower ∧ (cell13144 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13144 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13144 ⟨16,by decide⟩).lower ∧ (cell13144 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13144 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13144 ⟨17,by decide⟩).lower ∧ (cell13144 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13144 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13144 ⟨18,by decide⟩).lower ∧ (cell13144 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13144 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13144 ⟨19,by decide⟩).lower ∧ (cell13144 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13144 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13144 ⟨20,by decide⟩).lower ∧ (cell13144 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13144 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13144 ⟨21,by decide⟩).lower ∧ (cell13144 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13144 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13144 ⟨22,by decide⟩).lower ∧ (cell13144 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13144 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13144 ⟨23,by decide⟩).lower ∧ (cell13144 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13144 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13144 ⟨24,by decide⟩).lower ∧ (cell13144 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13144 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13144 ⟨25,by decide⟩).lower ∧ (cell13144 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13144 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13144 ⟨26,by decide⟩).lower ∧ (cell13144 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13144 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13144 ⟨27,by decide⟩).lower ∧ (cell13144 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13144 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13144 ⟨28,by decide⟩).lower ∧ (cell13144 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13144 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13144 ⟨29,by decide⟩).lower ∧ (cell13144 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13144 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13144 ⟨30,by decide⟩).lower ∧ (cell13144 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13144 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13144 ⟨31,by decide⟩).lower ∧ (cell13144 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13144 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13144 ⟨32,by decide⟩).lower ∧ (cell13144 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13144 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13144 ⟨33,by decide⟩).lower ∧ (cell13144 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13144 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13144 ⟨34,by decide⟩).lower ∧ (cell13144 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13144 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13144 ⟨35,by decide⟩).lower ∧ (cell13144 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13144 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13144 ⟨36,by decide⟩).lower ∧ (cell13144 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13144 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13144 ⟨37,by decide⟩).lower ∧ (cell13144 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13144 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13144 ⟨38,by decide⟩).lower ∧ (cell13144 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13144 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13144 ⟨39,by decide⟩).lower ∧ (cell13144 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13144 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13144 ⟨40,by decide⟩).lower ∧ (cell13144 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13144 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13144 ⟨41,by decide⟩).lower ∧ (cell13144 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13144 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13144 ⟨42,by decide⟩).lower ∧ (cell13144 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13144 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13144 ⟨43,by decide⟩).lower ∧ (cell13144 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13144 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13144 ⟨44,by decide⟩).lower ∧ (cell13144 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13144 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13144 ⟨45,by decide⟩).lower ∧ (cell13144 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13144 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13144 ⟨46,by decide⟩).lower ∧ (cell13144 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13144 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13144 ⟨47,by decide⟩).lower ∧ (cell13144 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13144 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13144 ⟨48,by decide⟩).lower ∧ (cell13144 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13144 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13144 ⟨49,by decide⟩).lower ∧ (cell13144 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13144 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13144 ⟨50,by decide⟩).lower ∧ (cell13144 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13144 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13144 ⟨51,by decide⟩).lower ∧ (cell13144 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13144 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13144 ⟨52,by decide⟩).lower ∧ (cell13144 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13144 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13144 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13144 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13144,cell13144,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13144 i).lower ∧
    (cell13144 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13144 i).upper ≤ (0.532 : ℝ) ∧
    (cell13144 i).centre ≤ (0.1 : ℝ) ∧ (cell13144 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13144 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13144 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13144

/-! The local source numeric instances at 13144 have no network premises. -/
namespace BstLean.Part269.N13144
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13144)
open BstLean.Part268 (cell13144)

noncomputable def sourceNumerics13144 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13144 (cell13144 i)
      scalarRow13144.M scalarRow13144.H scalarRow13144.xi := by
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
    energy_allowance := scalarRow13144.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13144]
    centre_nonneg := (scalarRow13144.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13144])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13144
/-! Actual 13145 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13145 ≤ (1.035192589214 : ℝ) := by
  have hr : (114.651646303051 : ℝ) ≤ √(13145 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.651646303051 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13145 13145 (11 / 1000) ≤
    (0.008337315124 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13145) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.651646303051 : ℝ) ≤ √(13145 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13145)
  have hdiv : K / √(13145 : ℝ) ≤ K / 114.651646303051 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.651646303051 ≤ (0.008337315124 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13145.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13145 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13145 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13145 := gPlus_lower 13145
end BstLean.Part269.N13145

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13145
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035192589213 : ℝ) ≤ wn 13145 := by
  have hn : √(13145 : ℝ) ≤ 114.651646303052 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13145 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.651646303052 ≤ 2 / √(13145 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243209030 : ℝ) ≤ rhoBar 13145 BstLean.Part154.csC ∧
    rhoBar 13145 BstLean.Part154.csC ≤ 0.000243209406 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035192589213 : ℝ) / (1.295212 * 13145) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035192589214 : ℝ) / (1.29521 * 13145) := by gcongr
      _ ≤ (0.000243209406 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13145 BstLean.Part154.csC) ≤ 0.000972896775 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13145 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) ≤ 0.000185764687 ∧
    cc1 (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) ≤ 0.000118203365 ∧
    cc2 (rhoBar 13145 BstLean.Part154.csC) ≤ 0.000068618034 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13145 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13145 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13145 BstLean.Part154.csC * nuR (rhoBar 13145 BstLean.Part154.csC)) ≤ 0.000486433600 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243209406 : ℝ) * 0.000972896775 := by gcongr
      _ ≤ (0.000486433600 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13145 BstLean.Part154.csC) * nuR (rhoBar 13145 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972896775 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13145 BstLean.Part154.csC) * rhoBar 13145 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243209406 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243209406 / 2 + 0.399 * 0.000972896775 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185764687 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486433600 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118203365 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243209406 / 1.414213562 := by gcongr
      _ ≤ (0.000068618034 : ℝ) := by norm_num

end BstLean.Part269.N13145

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13145
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) ≤ 1.49026E-7 := by
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13145 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13145 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13145 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185764687 : ℝ) ^ 2 + 0.000118203365 ^ 2 + 3 * 0.000068618034 ^ 2 +
        2 * 0.797885 * 0.000185764687 * 0.000118203365 + 2 * 0.000185764687 * 0.000068618034 +
        4 * 0.797885 * 0.000118203365 * 0.000068618034 := by gcongr
    _ ≤ (1.49026E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13145 BstLean.Part154.csC Θ ≤ 0.002537251365 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13145 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13145 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13145 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035192589214 * 1.49026E-7 / (0.000243209030 : ℝ) := by gcongr
    _ ≤ 0.002537251365 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13145 BstLean.Part154.csC Θ ≤ 0.002813539933 + 0.000641123545 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13145 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13145 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035192589214 : ℝ) * ((2 * Θ * 0.000243209406 +
        (6863 / 10000) * 0.000243209406 * 13145 * 0.000972896775) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002813539933 + 0.000641123545 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13145 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13145 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13145 0.011 Θ ∧ gammaRatio 13145 0.011 Θ ≤ 0.000083609105 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13145 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035192589214 : ℝ) * 0.525 / ((1 - 0.011) * 13145) := by gcongr
      _ ≤ (0.000083609105 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13145 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13145 0.011 Θ) :=
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
    badAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13145 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13145 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13145 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13145 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13145 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13145 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13145 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13145 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13145 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13145 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035192589214 : ℝ) * 13145 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003162628419 + 0.003178374910 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13145

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13145
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13145 BstLean.Part154.csC) (piBar (rhoBar 13145 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13145 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13145 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13145 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13145 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13145 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13145 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13145 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13145 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13145 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13145 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051578733627 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13145) ≤ 0.010416227064 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13145 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035192589214)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010416227064 + 2 * 0.737676 / 13145) := by gcongr
    _ ≤ (0.051578733627 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13145 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13145

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13145
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523011243 : ℝ) ≤ plow 13145 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13145) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337875247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332056967) : eMP 13145 0.011 xi bn ≤ 0.001147365552 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13145 : ℝ) * (1 - 0.011))) ≤ 0.000567358961 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332056967 / (13145 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567358961 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567358961 : ℝ) + 3.141593 * 0.052337875247 / (13145 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147365552 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337875247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332056967) : PiBarMP 13145 12 0.011 xi bn ≤ 0.158471286427 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13145 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036497355617 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.019318538570 : ℝ) ≤ √((13145 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.651646303051 : ℝ) ≤ √(13145 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13145) ≤ 0.121519478455 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036497355617 + 0.052337875247 * 1.772454 / (2 * (114.019318538570 : ℝ))) * (1 + 0.001147365552) +
        8 / (13145 * 114.651646303051) + 0.121519478455 := by gcongr
    _ ≤ (0.158471286427 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337875247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332056967) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280353459607) :
    parallelOracle 13145 0.011 xi bn cd ≤ 0.159428465716 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13145 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13145 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523011243 : ℝ) ≤ plow 13145 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.651646303051 : ℝ) ≤ √(13145 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280353459607 : ℝ) / (2 * 0.560523011243 * 114.651646303051)) * 0.158471286427 +
        0.280353459607 ^ 2 / (2 * 0.560523011243 * 114.651646303051) := by gcongr
    _ ≤ (0.159428465716 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337875247) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332056967)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280353459607) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13145 13145 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523011243 : ℝ) ≤ plow 13145 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.651646303051 : ℝ) ≤ √(13145 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13145 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13145 Θ 1.22 ≤ 0.011566345036 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.651646303051 := by gcongr <;> linarith
      _ ≤ (0.011566345036 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13145 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13145 13145 0.011 ≤ 0.008337315124 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13145 13145 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13145 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13145 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13145 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13145 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159428465716 + 0.011566345036 + (0.008337315124 : ℝ) *
        (1 + 2 * (0.280353459607 + 0.011566345036) / (0.560523011243 * 114.651646303051))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13145]

end BstLean.Part269.N13145

/-! The original eight local profiles supply actual 13145 moment certificates. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13145 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052337875247 ∧
    0 ≤ bN 13145 BstLean.Part154.csC (groupTheta g) ∧ bN 13145 BstLean.Part154.csC (groupTheta g) ≤ 0.001332056967 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13145 13145 0.011
      (momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13145 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13145 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13145 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228774725980 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13145 0.011
      (momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13145 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13145
/-! The actual computed-centre upper energy formula at 13145. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13145

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13145)
open BstLean.Part268 (cell13145)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084288542847
  | 2 => 0.085212486837
  | 3 => 0.086131945251
  | 4 => 0.087047718108
  | 5 => 0.087960790560
  | 6 => 0.088872362508
  | 7 => 0.089783881426
  | 8 => 0.090697078482
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13145 13145 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13145 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13145

/-! Actual upper energy certificates on all 43 source endpoints at 13145. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13145)
open BstLean.Part268 (cell13145)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13145 (gMinus 13145) (1 - (cell13145 i).lower) ≤ 1 ∧
    energyUpper 13145 (gMinus 13145) (BstLean.Part211.gPlus 13145)
      (finiteEnergy 13145 13145 0.011) (1 - (cell13145 i).lower) ≤
      (cell13145 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨10,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨11,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨12,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨13,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨14,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨15,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨16,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨17,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨18,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨19,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨20,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨21,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨22,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨23,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨24,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨25,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨26,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨27,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨28,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨29,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨30,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨31,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨32,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨33,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨34,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨35,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨36,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨37,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨38,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨39,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨40,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨41,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨42,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨43,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨44,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨45,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨46,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨47,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨48,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨49,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨50,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨51,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13145) (by norm_num)
        (q := 1 - (cell13145 ⟨52,by decide⟩).lower)
        (by norm_num [cell13145]) (by norm_num [cell13145])
      exact ⟨E.1,E.2.trans (by norm_num [cell13145])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13145

/-! Source-cell containment and simple scalar guards at 13145. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13145)
open BstLean.Part268 (cell13145)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13145 ⟨10,by decide⟩).lower ∧ (cell13145 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13145 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13145 ⟨11,by decide⟩).lower ∧ (cell13145 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13145 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13145 ⟨12,by decide⟩).lower ∧ (cell13145 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13145 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13145 ⟨13,by decide⟩).lower ∧ (cell13145 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13145 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13145 ⟨14,by decide⟩).lower ∧ (cell13145 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13145 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13145 ⟨15,by decide⟩).lower ∧ (cell13145 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13145 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13145 ⟨16,by decide⟩).lower ∧ (cell13145 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13145 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13145 ⟨17,by decide⟩).lower ∧ (cell13145 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13145 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13145 ⟨18,by decide⟩).lower ∧ (cell13145 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13145 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13145 ⟨19,by decide⟩).lower ∧ (cell13145 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13145 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13145 ⟨20,by decide⟩).lower ∧ (cell13145 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13145 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13145 ⟨21,by decide⟩).lower ∧ (cell13145 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13145 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13145 ⟨22,by decide⟩).lower ∧ (cell13145 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13145 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13145 ⟨23,by decide⟩).lower ∧ (cell13145 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13145 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13145 ⟨24,by decide⟩).lower ∧ (cell13145 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13145 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13145 ⟨25,by decide⟩).lower ∧ (cell13145 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13145 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13145 ⟨26,by decide⟩).lower ∧ (cell13145 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13145 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13145 ⟨27,by decide⟩).lower ∧ (cell13145 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13145 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13145 ⟨28,by decide⟩).lower ∧ (cell13145 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13145 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13145 ⟨29,by decide⟩).lower ∧ (cell13145 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13145 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13145 ⟨30,by decide⟩).lower ∧ (cell13145 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13145 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13145 ⟨31,by decide⟩).lower ∧ (cell13145 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13145 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13145 ⟨32,by decide⟩).lower ∧ (cell13145 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13145 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13145 ⟨33,by decide⟩).lower ∧ (cell13145 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13145 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13145 ⟨34,by decide⟩).lower ∧ (cell13145 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13145 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13145 ⟨35,by decide⟩).lower ∧ (cell13145 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13145 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13145 ⟨36,by decide⟩).lower ∧ (cell13145 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13145 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13145 ⟨37,by decide⟩).lower ∧ (cell13145 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13145 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13145 ⟨38,by decide⟩).lower ∧ (cell13145 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13145 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13145 ⟨39,by decide⟩).lower ∧ (cell13145 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13145 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13145 ⟨40,by decide⟩).lower ∧ (cell13145 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13145 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13145 ⟨41,by decide⟩).lower ∧ (cell13145 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13145 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13145 ⟨42,by decide⟩).lower ∧ (cell13145 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13145 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13145 ⟨43,by decide⟩).lower ∧ (cell13145 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13145 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13145 ⟨44,by decide⟩).lower ∧ (cell13145 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13145 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13145 ⟨45,by decide⟩).lower ∧ (cell13145 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13145 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13145 ⟨46,by decide⟩).lower ∧ (cell13145 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13145 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13145 ⟨47,by decide⟩).lower ∧ (cell13145 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13145 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13145 ⟨48,by decide⟩).lower ∧ (cell13145 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13145 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13145 ⟨49,by decide⟩).lower ∧ (cell13145 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13145 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13145 ⟨50,by decide⟩).lower ∧ (cell13145 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13145 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13145 ⟨51,by decide⟩).lower ∧ (cell13145 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13145 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13145 ⟨52,by decide⟩).lower ∧ (cell13145 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13145 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13145 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13145 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13145,cell13145,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13145 i).lower ∧
    (cell13145 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13145 i).upper ≤ (0.532 : ℝ) ∧
    (cell13145 i).centre ≤ (0.1 : ℝ) ∧ (cell13145 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13145 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13145 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13145

/-! The local source numeric instances at 13145 have no network premises. -/
namespace BstLean.Part269.N13145
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13145)
open BstLean.Part268 (cell13145)

noncomputable def sourceNumerics13145 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13145 (cell13145 i)
      scalarRow13145.M scalarRow13145.H scalarRow13145.xi := by
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
    energy_allowance := scalarRow13145.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13145]
    centre_nonneg := (scalarRow13145.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13145])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13145
/-! Actual 13146 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13146 ≤ (1.035191239087 : ℝ) := by
  have hr : (114.656007256488 : ℝ) ≤ √(13146 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.656007256488 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13146 13146 (11 / 1000) ≤
    (0.008336998011 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13146) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.656007256488 : ℝ) ≤ √(13146 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13146)
  have hdiv : K / √(13146 : ℝ) ≤ K / 114.656007256488 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.656007256488 ≤ (0.008336998011 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13146.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13146 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13146 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13146 := gPlus_lower 13146
end BstLean.Part269.N13146

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13146
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035191239086 : ℝ) ≤ wn 13146 := by
  have hn : √(13146 : ℝ) ≤ 114.656007256489 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13146 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.656007256489 ≤ 2 / √(13146 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243190212 : ℝ) ≤ rhoBar 13146 BstLean.Part154.csC ∧
    rhoBar 13146 BstLean.Part154.csC ≤ 0.000243190588 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035191239086 : ℝ) / (1.295212 * 13146) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035191239087 : ℝ) / (1.29521 * 13146) := by gcongr
      _ ≤ (0.000243190588 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13146 BstLean.Part154.csC) ≤ 0.000972821494 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13146 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) ≤ 0.000185750314 ∧
    cc1 (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) ≤ 0.000118194219 ∧
    cc2 (rhoBar 13146 BstLean.Part154.csC) ≤ 0.000068612724 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13146 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13146 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13146 BstLean.Part154.csC * nuR (rhoBar 13146 BstLean.Part154.csC)) ≤ 0.000486395962 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243190588 : ℝ) * 0.000972821494 := by gcongr
      _ ≤ (0.000486395962 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13146 BstLean.Part154.csC) * nuR (rhoBar 13146 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972821494 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13146 BstLean.Part154.csC) * rhoBar 13146 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243190588 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243190588 / 2 + 0.399 * 0.000972821494 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185750314 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486395962 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118194219 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243190588 / 1.414213562 := by gcongr
      _ ≤ (0.000068612724 : ℝ) := by norm_num

end BstLean.Part269.N13146

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13146
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) ≤ 1.49003E-7 := by
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13146 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13146 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13146 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185750314 : ℝ) ^ 2 + 0.000118194219 ^ 2 + 3 * 0.000068612724 ^ 2 +
        2 * 0.797885 * 0.000185750314 * 0.000118194219 + 2 * 0.000185750314 * 0.000068612724 +
        4 * 0.797885 * 0.000118194219 * 0.000068612724 := by gcongr
    _ ≤ (1.49003E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13146 BstLean.Part154.csC Θ ≤ 0.002537052770 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13146 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13146 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13146 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035191239087 * 1.49003E-7 / (0.000243190212 : ℝ) := by gcongr
    _ ≤ 0.002537052770 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13146 BstLean.Part154.csC Θ ≤ 0.002813314886 + 0.000641073103 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13146 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13146 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035191239087 : ℝ) * ((2 * Θ * 0.000243190588 +
        (6863 / 10000) * 0.000243190588 * 13146 * 0.000972821494) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002813314886 + 0.000641073103 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13146 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13146 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13146 0.011 Θ ∧ gammaRatio 13146 0.011 Θ ≤ 0.000083602636 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13146 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035191239087 : ℝ) * 0.525 / ((1 - 0.011) * 13146) := by gcongr
      _ ≤ (0.000083602636 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13146 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13146 0.011 Θ) :=
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
    badAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13146 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13146 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13146 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13146 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13146 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13146 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13146 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13146 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13146 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13146 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035191239087 : ℝ) * 13146 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003162403372 + 0.003178125873 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13146

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13146
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13146 BstLean.Part154.csC) (piBar (rhoBar 13146 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13146 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13146 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13146 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13146 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13146 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13146 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13146 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13146 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13146 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13146 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051576750908 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13146) ≤ 0.010415830881 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13146 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035191239087)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010415830881 + 2 * 0.737676 / 13146) := by gcongr
    _ ≤ (0.051576750908 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13146 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13146

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13146
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523053453 : ℝ) ≤ plow 13146 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13146) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337519456)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331952705) : eMP 13146 0.011 xi bn ≤ 0.001147276938 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13146 : ℝ) * (1 - 0.011))) ≤ 0.000567315178 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331952705 / (13146 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567315178 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567315178 : ℝ) + 3.141593 * 0.052337519456 / (13146 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147276938 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337519456)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331952705) : PiBarMP 13146 12 0.011 xi bn ≤ 0.158465212269 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13146 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036495927239 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.023655440439 : ℝ) ≤ √((13146 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.656007256488 : ℝ) ≤ √(13146 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13146) ≤ 0.121514856449 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036495927239 + 0.052337519456 * 1.772454 / (2 * (114.023655440439 : ℝ))) * (1 + 0.001147276938) +
        8 / (13146 * 114.656007256488) + 0.121514856449 := by gcongr
    _ ≤ (0.158465212269 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337519456)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331952705) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280350699285) :
    parallelOracle 13146 0.011 xi bn cd ≤ 0.159422326386 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13146 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13146 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523053453 : ℝ) ≤ plow 13146 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.656007256488 : ℝ) ≤ √(13146 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280350699285 : ℝ) / (2 * 0.560523053453 * 114.656007256488)) * 0.158465212269 +
        0.280350699285 ^ 2 / (2 * 0.560523053453 * 114.656007256488) := by gcongr
    _ ≤ (0.159422326386 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337519456) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331952705)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280350699285) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13146 13146 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523053453 : ℝ) ≤ plow 13146 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.656007256488 : ℝ) ≤ √(13146 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13146 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13146 Θ 1.22 ≤ 0.011565905109 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.656007256488 := by gcongr <;> linarith
      _ ≤ (0.011565905109 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13146 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13146 13146 0.011 ≤ 0.008336998011 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13146 13146 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13146 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13146 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13146 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13146 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159422326386 + 0.011565905109 + (0.008336998011 : ℝ) *
        (1 + 2 * (0.280350699285 + 0.011565905109) / (0.560523053453 * 114.656007256488))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13146]

end BstLean.Part269.N13146

/-! The original eight local profiles supply actual 13146 moment certificates. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13146 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052337519456 ∧
    0 ≤ bN 13146 BstLean.Part154.csC (groupTheta g) ∧ bN 13146 BstLean.Part154.csC (groupTheta g) ≤ 0.001331952705 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13146 13146 0.011
      (momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13146 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13146 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13146 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228773948377 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13146 0.011
      (momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13146 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13146
/-! The actual computed-centre upper energy formula at 13146. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13146

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13146)
open BstLean.Part268 (cell13146)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084286034297
  | 2 => 0.085209947511
  | 3 => 0.086129370803
  | 4 => 0.087045103152
  | 5 => 0.087958128476
  | 6 => 0.088869645222
  | 7 => 0.089781099161
  | 8 => 0.090694219481
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13146 13146 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13146 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13146

/-! Actual upper energy certificates on all 43 source endpoints at 13146. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13146)
open BstLean.Part268 (cell13146)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13146 (gMinus 13146) (1 - (cell13146 i).lower) ≤ 1 ∧
    energyUpper 13146 (gMinus 13146) (BstLean.Part211.gPlus 13146)
      (finiteEnergy 13146 13146 0.011) (1 - (cell13146 i).lower) ≤
      (cell13146 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨10,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨11,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨12,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨13,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨14,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨15,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨16,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨17,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨18,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨19,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨20,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨21,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨22,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨23,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨24,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨25,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨26,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨27,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨28,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨29,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨30,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨31,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨32,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨33,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨34,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨35,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨36,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨37,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨38,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨39,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨40,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨41,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨42,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨43,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨44,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨45,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨46,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨47,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨48,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨49,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨50,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨51,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13146) (by norm_num)
        (q := 1 - (cell13146 ⟨52,by decide⟩).lower)
        (by norm_num [cell13146]) (by norm_num [cell13146])
      exact ⟨E.1,E.2.trans (by norm_num [cell13146])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13146

/-! Source-cell containment and simple scalar guards at 13146. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13146)
open BstLean.Part268 (cell13146)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13146 ⟨10,by decide⟩).lower ∧ (cell13146 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13146 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13146 ⟨11,by decide⟩).lower ∧ (cell13146 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13146 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13146 ⟨12,by decide⟩).lower ∧ (cell13146 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13146 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13146 ⟨13,by decide⟩).lower ∧ (cell13146 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13146 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13146 ⟨14,by decide⟩).lower ∧ (cell13146 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13146 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13146 ⟨15,by decide⟩).lower ∧ (cell13146 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13146 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13146 ⟨16,by decide⟩).lower ∧ (cell13146 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13146 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13146 ⟨17,by decide⟩).lower ∧ (cell13146 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13146 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13146 ⟨18,by decide⟩).lower ∧ (cell13146 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13146 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13146 ⟨19,by decide⟩).lower ∧ (cell13146 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13146 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13146 ⟨20,by decide⟩).lower ∧ (cell13146 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13146 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13146 ⟨21,by decide⟩).lower ∧ (cell13146 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13146 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13146 ⟨22,by decide⟩).lower ∧ (cell13146 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13146 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13146 ⟨23,by decide⟩).lower ∧ (cell13146 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13146 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13146 ⟨24,by decide⟩).lower ∧ (cell13146 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13146 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13146 ⟨25,by decide⟩).lower ∧ (cell13146 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13146 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13146 ⟨26,by decide⟩).lower ∧ (cell13146 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13146 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13146 ⟨27,by decide⟩).lower ∧ (cell13146 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13146 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13146 ⟨28,by decide⟩).lower ∧ (cell13146 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13146 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13146 ⟨29,by decide⟩).lower ∧ (cell13146 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13146 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13146 ⟨30,by decide⟩).lower ∧ (cell13146 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13146 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13146 ⟨31,by decide⟩).lower ∧ (cell13146 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13146 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13146 ⟨32,by decide⟩).lower ∧ (cell13146 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13146 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13146 ⟨33,by decide⟩).lower ∧ (cell13146 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13146 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13146 ⟨34,by decide⟩).lower ∧ (cell13146 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13146 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13146 ⟨35,by decide⟩).lower ∧ (cell13146 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13146 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13146 ⟨36,by decide⟩).lower ∧ (cell13146 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13146 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13146 ⟨37,by decide⟩).lower ∧ (cell13146 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13146 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13146 ⟨38,by decide⟩).lower ∧ (cell13146 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13146 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13146 ⟨39,by decide⟩).lower ∧ (cell13146 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13146 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13146 ⟨40,by decide⟩).lower ∧ (cell13146 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13146 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13146 ⟨41,by decide⟩).lower ∧ (cell13146 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13146 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13146 ⟨42,by decide⟩).lower ∧ (cell13146 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13146 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13146 ⟨43,by decide⟩).lower ∧ (cell13146 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13146 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13146 ⟨44,by decide⟩).lower ∧ (cell13146 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13146 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13146 ⟨45,by decide⟩).lower ∧ (cell13146 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13146 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13146 ⟨46,by decide⟩).lower ∧ (cell13146 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13146 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13146 ⟨47,by decide⟩).lower ∧ (cell13146 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13146 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13146 ⟨48,by decide⟩).lower ∧ (cell13146 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13146 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13146 ⟨49,by decide⟩).lower ∧ (cell13146 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13146 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13146 ⟨50,by decide⟩).lower ∧ (cell13146 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13146 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13146 ⟨51,by decide⟩).lower ∧ (cell13146 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13146 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13146 ⟨52,by decide⟩).lower ∧ (cell13146 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13146 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13146 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13146 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13146,cell13146,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13146 i).lower ∧
    (cell13146 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13146 i).upper ≤ (0.532 : ℝ) ∧
    (cell13146 i).centre ≤ (0.1 : ℝ) ∧ (cell13146 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13146 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13146 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13146

/-! The local source numeric instances at 13146 have no network premises. -/
namespace BstLean.Part269.N13146
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13146)
open BstLean.Part268 (cell13146)

noncomputable def sourceNumerics13146 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13146 (cell13146 i)
      scalarRow13146.M scalarRow13146.H scalarRow13146.xi := by
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
    energy_allowance := scalarRow13146.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13146]
    centre_nonneg := (scalarRow13146.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13146])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13146
/-! Actual 13147 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13147 ≤ (1.035189889114 : ℝ) := by
  have hr : (114.660368044063 : ℝ) ≤ √(13147 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.660368044063 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13147 13147 (11 / 1000) ≤
    (0.008336680934 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13147) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.660368044063 : ℝ) ≤ √(13147 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13147)
  have hdiv : K / √(13147 : ℝ) ≤ K / 114.660368044063 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.660368044063 ≤ (0.008336680934 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13147.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13147 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13147 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13147 := gPlus_lower 13147
end BstLean.Part269.N13147

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13147
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035189889113 : ℝ) ≤ wn 13147 := by
  have hn : √(13147 : ℝ) ≤ 114.660368044064 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13147 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.660368044064 ≤ 2 / √(13147 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243171397 : ℝ) ≤ rhoBar 13147 BstLean.Part154.csC ∧
    rhoBar 13147 BstLean.Part154.csC ≤ 0.000243171773 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035189889113 : ℝ) / (1.295212 * 13147) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035189889114 : ℝ) / (1.29521 * 13147) := by gcongr
      _ ≤ (0.000243171773 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13147 BstLean.Part154.csC) ≤ 0.000972746225 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13147 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) ≤ 0.000185735942 ∧
    cc1 (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) ≤ 0.000118185075 ∧
    cc2 (rhoBar 13147 BstLean.Part154.csC) ≤ 0.000068607416 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13147 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13147 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13147 BstLean.Part154.csC * nuR (rhoBar 13147 BstLean.Part154.csC)) ≤ 0.000486358330 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243171773 : ℝ) * 0.000972746225 := by gcongr
      _ ≤ (0.000486358330 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13147 BstLean.Part154.csC) * nuR (rhoBar 13147 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972746225 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13147 BstLean.Part154.csC) * rhoBar 13147 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243171773 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243171773 / 2 + 0.399 * 0.000972746225 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185735942 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486358330 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118185075 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243171773 / 1.414213562 := by gcongr
      _ ≤ (0.000068607416 : ℝ) := by norm_num

end BstLean.Part269.N13147

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13147
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) ≤ 1.48980E-7 := by
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13147 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13147 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13147 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185735942 : ℝ) ^ 2 + 0.000118185075 ^ 2 + 3 * 0.000068607416 ^ 2 +
        2 * 0.797885 * 0.000185735942 * 0.000118185075 + 2 * 0.000185735942 * 0.000068607416 +
        4 * 0.797885 * 0.000118185075 * 0.000068607416 := by gcongr
    _ ≤ (1.48980E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13147 BstLean.Part154.csC Θ ≤ 0.002536854114 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13147 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13147 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13147 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035189889114 * 1.48980E-7 / (0.000243171397 : ℝ) := by gcongr
    _ ≤ 0.002536854114 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13147 BstLean.Part154.csC Θ ≤ 0.002813089876 + 0.000641022669 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13147 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13147 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035189889114 : ℝ) * ((2 * Θ * 0.000243171773 +
        (6863 / 10000) * 0.000243171773 * 13147 * 0.000972746225) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002813089876 + 0.000641022669 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13147 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13147 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13147 0.011 Θ ∧ gammaRatio 13147 0.011 Θ ≤ 0.000083596168 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13147 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035189889114 : ℝ) * 0.525 / ((1 - 0.011) * 13147) := by gcongr
      _ ≤ (0.000083596168 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13147 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13147 0.011 Θ) :=
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
    badAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13147 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13147 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13147 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13147 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13147 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13147 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13147 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13147 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13147 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13147 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035189889114 : ℝ) * 13147 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003162178362 + 0.003177876783 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13147

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13147
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13147 BstLean.Part154.csC) (piBar (rhoBar 13147 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13147 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13147 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13147 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13147 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13147 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13147 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13147 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13147 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13147 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13147 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051574768421 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13147) ≤ 0.010415434744 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13147 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035189889114)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010415434744 + 2 * 0.737676 / 13147) := by gcongr
    _ ≤ (0.051574768421 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13147 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13147

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13147
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523095656 : ℝ) ≤ plow 13147 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13147) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337163674)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331848410) : eMP 13147 0.011 xi bn ≤ 0.001147188316 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13147 : ℝ) * (1 - 0.011))) ≤ 0.000567271391 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331848410 / (13147 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567271391 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567271391 : ℝ) + 3.141593 * 0.052337163674 / (13147 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147188316 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337163674)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331848410) : PiBarMP 13147 12 0.011 xi bn ≤ 0.158459138132 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13147 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036494498353 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.027992177359 : ℝ) ≤ √((13147 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.660368044063 : ℝ) ≤ √(13147 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13147) ≤ 0.121510234970 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036494498353 + 0.052337163674 * 1.772454 / (2 * (114.027992177359 : ℝ))) * (1 + 0.001147188316) +
        8 / (13147 * 114.660368044063) + 0.121510234970 := by gcongr
    _ ≤ (0.158459138132 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337163674)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331848410) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280347939213) :
    parallelOracle 13147 0.011 xi bn cd ≤ 0.159416187086 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13147 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13147 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523095656 : ℝ) ≤ plow 13147 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.660368044063 : ℝ) ≤ √(13147 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280347939213 : ℝ) / (2 * 0.560523095656 * 114.660368044063)) * 0.158459138132 +
        0.280347939213 ^ 2 / (2 * 0.560523095656 * 114.660368044063) := by gcongr
    _ ≤ (0.159416187086 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052337163674) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331848410)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280347939213) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13147 13147 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523095656 : ℝ) ≤ plow 13147 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.660368044063 : ℝ) ≤ √(13147 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13147 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13147 Θ 1.22 ≤ 0.011565465232 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.660368044063 := by gcongr <;> linarith
      _ ≤ (0.011565465232 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13147 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13147 13147 0.011 ≤ 0.008336680934 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13147 13147 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13147 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13147 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13147 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13147 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159416187086 + 0.011565465232 + (0.008336680934 : ℝ) *
        (1 + 2 * (0.280347939213 + 0.011565465232) / (0.560523095656 * 114.660368044063))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13147]

end BstLean.Part269.N13147

/-! The original eight local profiles supply actual 13147 moment certificates. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13147 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052337163674 ∧
    0 ≤ bN 13147 BstLean.Part154.csC (groupTheta g) ∧ bN 13147 BstLean.Part154.csC (groupTheta g) ≤ 0.001331848410 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13147 13147 0.011
      (momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13147 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13147 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13147 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228773170792 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13147 0.011
      (momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13147 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13147
/-! The actual computed-centre upper energy formula at 13147. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13147

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13147)
open BstLean.Part268 (cell13147)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084283526455
  | 2 => 0.085207408917
  | 3 => 0.086126797116
  | 4 => 0.087042488994
  | 5 => 0.087955467234
  | 6 => 0.088866928832
  | 7 => 0.089778317859
  | 8 => 0.090691361523
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13147 13147 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13147 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13147

/-! Actual upper energy certificates on all 43 source endpoints at 13147. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13147)
open BstLean.Part268 (cell13147)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13147 (gMinus 13147) (1 - (cell13147 i).lower) ≤ 1 ∧
    energyUpper 13147 (gMinus 13147) (BstLean.Part211.gPlus 13147)
      (finiteEnergy 13147 13147 0.011) (1 - (cell13147 i).lower) ≤
      (cell13147 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨10,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨11,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨12,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨13,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨14,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨15,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨16,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨17,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨18,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨19,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨20,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨21,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨22,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨23,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨24,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨25,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨26,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨27,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨28,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨29,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨30,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨31,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨32,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨33,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨34,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨35,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨36,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨37,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨38,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨39,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨40,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨41,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨42,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨43,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨44,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨45,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨46,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨47,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨48,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨49,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨50,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨51,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13147) (by norm_num)
        (q := 1 - (cell13147 ⟨52,by decide⟩).lower)
        (by norm_num [cell13147]) (by norm_num [cell13147])
      exact ⟨E.1,E.2.trans (by norm_num [cell13147])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13147

/-! Source-cell containment and simple scalar guards at 13147. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13147)
open BstLean.Part268 (cell13147)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13147 ⟨10,by decide⟩).lower ∧ (cell13147 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13147 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13147 ⟨11,by decide⟩).lower ∧ (cell13147 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13147 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13147 ⟨12,by decide⟩).lower ∧ (cell13147 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13147 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13147 ⟨13,by decide⟩).lower ∧ (cell13147 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13147 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13147 ⟨14,by decide⟩).lower ∧ (cell13147 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13147 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13147 ⟨15,by decide⟩).lower ∧ (cell13147 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13147 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13147 ⟨16,by decide⟩).lower ∧ (cell13147 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13147 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13147 ⟨17,by decide⟩).lower ∧ (cell13147 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13147 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13147 ⟨18,by decide⟩).lower ∧ (cell13147 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13147 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13147 ⟨19,by decide⟩).lower ∧ (cell13147 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13147 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13147 ⟨20,by decide⟩).lower ∧ (cell13147 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13147 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13147 ⟨21,by decide⟩).lower ∧ (cell13147 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13147 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13147 ⟨22,by decide⟩).lower ∧ (cell13147 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13147 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13147 ⟨23,by decide⟩).lower ∧ (cell13147 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13147 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13147 ⟨24,by decide⟩).lower ∧ (cell13147 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13147 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13147 ⟨25,by decide⟩).lower ∧ (cell13147 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13147 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13147 ⟨26,by decide⟩).lower ∧ (cell13147 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13147 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13147 ⟨27,by decide⟩).lower ∧ (cell13147 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13147 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13147 ⟨28,by decide⟩).lower ∧ (cell13147 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13147 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13147 ⟨29,by decide⟩).lower ∧ (cell13147 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13147 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13147 ⟨30,by decide⟩).lower ∧ (cell13147 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13147 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13147 ⟨31,by decide⟩).lower ∧ (cell13147 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13147 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13147 ⟨32,by decide⟩).lower ∧ (cell13147 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13147 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13147 ⟨33,by decide⟩).lower ∧ (cell13147 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13147 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13147 ⟨34,by decide⟩).lower ∧ (cell13147 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13147 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13147 ⟨35,by decide⟩).lower ∧ (cell13147 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13147 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13147 ⟨36,by decide⟩).lower ∧ (cell13147 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13147 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13147 ⟨37,by decide⟩).lower ∧ (cell13147 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13147 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13147 ⟨38,by decide⟩).lower ∧ (cell13147 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13147 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13147 ⟨39,by decide⟩).lower ∧ (cell13147 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13147 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13147 ⟨40,by decide⟩).lower ∧ (cell13147 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13147 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13147 ⟨41,by decide⟩).lower ∧ (cell13147 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13147 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13147 ⟨42,by decide⟩).lower ∧ (cell13147 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13147 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13147 ⟨43,by decide⟩).lower ∧ (cell13147 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13147 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13147 ⟨44,by decide⟩).lower ∧ (cell13147 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13147 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13147 ⟨45,by decide⟩).lower ∧ (cell13147 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13147 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13147 ⟨46,by decide⟩).lower ∧ (cell13147 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13147 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13147 ⟨47,by decide⟩).lower ∧ (cell13147 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13147 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13147 ⟨48,by decide⟩).lower ∧ (cell13147 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13147 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13147 ⟨49,by decide⟩).lower ∧ (cell13147 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13147 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13147 ⟨50,by decide⟩).lower ∧ (cell13147 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13147 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13147 ⟨51,by decide⟩).lower ∧ (cell13147 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13147 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13147 ⟨52,by decide⟩).lower ∧ (cell13147 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13147 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13147 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13147 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13147,cell13147,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13147 i).lower ∧
    (cell13147 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13147 i).upper ≤ (0.532 : ℝ) ∧
    (cell13147 i).centre ≤ (0.1 : ℝ) ∧ (cell13147 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13147 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13147 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13147

/-! The local source numeric instances at 13147 have no network premises. -/
namespace BstLean.Part269.N13147
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13147)
open BstLean.Part268 (cell13147)

noncomputable def sourceNumerics13147 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13147 (cell13147 i)
      scalarRow13147.M scalarRow13147.H scalarRow13147.xi := by
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
    energy_allowance := scalarRow13147.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13147]
    centre_nonneg := (scalarRow13147.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13147])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13147
/-! Actual 13148 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13148 ≤ (1.035188539296 : ℝ) := by
  have hr : (114.664728665793 : ℝ) ≤ √(13148 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.664728665793 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13148 13148 (11 / 1000) ≤
    (0.008336363893 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13148) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.664728665793 : ℝ) ≤ √(13148 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13148)
  have hdiv : K / √(13148 : ℝ) ≤ K / 114.664728665793 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.664728665793 ≤ (0.008336363893 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13148.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13148 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13148 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13148 := gPlus_lower 13148
end BstLean.Part269.N13148

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13148
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035188539295 : ℝ) ≤ wn 13148 := by
  have hn : √(13148 : ℝ) ≤ 114.664728665794 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13148 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.664728665794 ≤ 2 / √(13148 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243152585 : ℝ) ≤ rhoBar 13148 BstLean.Part154.csC ∧
    rhoBar 13148 BstLean.Part154.csC ≤ 0.000243152961 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035188539295 : ℝ) / (1.295212 * 13148) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035188539296 : ℝ) / (1.29521 * 13148) := by gcongr
      _ ≤ (0.000243152961 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13148 BstLean.Part154.csC) ≤ 0.000972670968 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13148 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) ≤ 0.000185721573 ∧
    cc1 (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) ≤ 0.000118175931 ∧
    cc2 (rhoBar 13148 BstLean.Part154.csC) ≤ 0.000068602108 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13148 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13148 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13148 BstLean.Part154.csC * nuR (rhoBar 13148 BstLean.Part154.csC)) ≤ 0.000486320703 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243152961 : ℝ) * 0.000972670968 := by gcongr
      _ ≤ (0.000486320703 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13148 BstLean.Part154.csC) * nuR (rhoBar 13148 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972670968 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13148 BstLean.Part154.csC) * rhoBar 13148 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243152961 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243152961 / 2 + 0.399 * 0.000972670968 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185721573 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486320703 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118175931 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243152961 / 1.414213562 := by gcongr
      _ ≤ (0.000068602108 : ℝ) := by norm_num

end BstLean.Part269.N13148

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13148
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) ≤ 1.48957E-7 := by
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13148 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13148 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13148 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185721573 : ℝ) ^ 2 + 0.000118175931 ^ 2 + 3 * 0.000068602108 ^ 2 +
        2 * 0.797885 * 0.000185721573 * 0.000118175931 + 2 * 0.000185721573 * 0.000068602108 +
        4 * 0.797885 * 0.000118175931 * 0.000068602108 := by gcongr
    _ ≤ (1.48957E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13148 BstLean.Part154.csC Θ ≤ 0.002536655397 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13148 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13148 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13148 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035188539296 * 1.48957E-7 / (0.000243152585 : ℝ) := by gcongr
    _ ≤ 0.002536655397 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13148 BstLean.Part154.csC Θ ≤ 0.002812864905 + 0.000640972243 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13148 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13148 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035188539296 : ℝ) * ((2 * Θ * 0.000243152961 +
        (6863 / 10000) * 0.000243152961 * 13148 * 0.000972670968) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002812864905 + 0.000640972243 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13148 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13148 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13148 0.011 Θ ∧ gammaRatio 13148 0.011 Θ ≤ 0.000083589701 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13148 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035188539296 : ℝ) * 0.525 / ((1 - 0.011) * 13148) := by gcongr
      _ ≤ (0.000083589701 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13148 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13148 0.011 Θ) :=
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
    badAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13148 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13148 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13148 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13148 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13148 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13148 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13148 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13148 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13148 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13148 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035188539296 : ℝ) * 13148 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003161953391 + 0.003177627640 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13148

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13148
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13148 BstLean.Part154.csC) (piBar (rhoBar 13148 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13148 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13148 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13148 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13148 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13148 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13148 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13148 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13148 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13148 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13148 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051572786161 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13148) ≤ 0.010415038652 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13148 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035188539296)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010415038652 + 2 * 0.737676 / 13148) := by gcongr
    _ ≤ (0.051572786161 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13148 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13148

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13148
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523137853 : ℝ) ≤ plow 13148 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13148) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336807902)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331744084) : eMP 13148 0.011 xi bn ≤ 0.001147099688 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13148 : ℝ) * (1 - 0.011))) ≤ 0.000567227601 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331744084 / (13148 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567227601 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567227601 : ℝ) + 3.141593 * 0.052336807902 / (13148 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147099688 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336807902)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331744084) : PiBarMP 13148 12 0.011 xi bn ≤ 0.158453064044 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13148 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036493068986 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.032328749350 : ℝ) ≤ √((13148 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.664728665793 : ℝ) ≤ √(13148 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13148) ≤ 0.121505614019 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036493068986 + 0.052336807902 * 1.772454 / (2 * (114.032328749350 : ℝ))) * (1 + 0.001147099688) +
        8 / (13148 * 114.664728665793) + 0.121505614019 := by gcongr
    _ ≤ (0.158453064044 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336807902)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331744084) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280345179387) :
    parallelOracle 13148 0.011 xi bn cd ≤ 0.159410047843 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13148 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13148 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523137853 : ℝ) ≤ plow 13148 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.664728665793 : ℝ) ≤ √(13148 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280345179387 : ℝ) / (2 * 0.560523137853 * 114.664728665793)) * 0.158453064044 +
        0.280345179387 ^ 2 / (2 * 0.560523137853 * 114.664728665793) := by gcongr
    _ ≤ (0.159410047843 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336807902) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331744084)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280345179387) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13148 13148 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523137853 : ℝ) ≤ plow 13148 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.664728665793 : ℝ) ≤ √(13148 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13148 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13148 Θ 1.22 ≤ 0.011565025405 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.664728665793 := by gcongr <;> linarith
      _ ≤ (0.011565025405 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13148 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13148 13148 0.011 ≤ 0.008336363893 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13148 13148 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13148 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13148 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13148 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13148 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159410047843 + 0.011565025405 + (0.008336363893 : ℝ) *
        (1 + 2 * (0.280345179387 + 0.011565025405) / (0.560523137853 * 114.664728665793))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13148]

end BstLean.Part269.N13148

/-! The original eight local profiles supply actual 13148 moment certificates. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13148 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052336807902 ∧
    0 ≤ bN 13148 BstLean.Part154.csC (groupTheta g) ∧ bN 13148 BstLean.Part154.csC (groupTheta g) ≤ 0.001331744084 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13148 13148 0.011
      (momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13148 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13148 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13148 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228772393226 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13148 0.011
      (momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13148 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13148
/-! The actual computed-centre upper energy formula at 13148. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13148

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13148)
open BstLean.Part268 (cell13148)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084281019321
  | 2 => 0.085204871054
  | 3 => 0.086124224190
  | 4 => 0.087039875632
  | 5 => 0.087952806833
  | 6 => 0.088864213338
  | 7 => 0.089775537519
  | 8 => 0.090688504607
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13148 13148 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13148 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13148

/-! Actual upper energy certificates on all 43 source endpoints at 13148. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13148)
open BstLean.Part268 (cell13148)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13148 (gMinus 13148) (1 - (cell13148 i).lower) ≤ 1 ∧
    energyUpper 13148 (gMinus 13148) (BstLean.Part211.gPlus 13148)
      (finiteEnergy 13148 13148 0.011) (1 - (cell13148 i).lower) ≤
      (cell13148 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨10,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨11,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨12,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨13,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨14,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨15,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨16,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨17,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨18,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨19,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨20,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨21,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨22,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨23,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨24,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨25,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨26,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨27,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨28,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨29,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨30,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨31,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨32,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨33,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨34,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨35,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨36,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨37,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨38,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨39,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨40,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨41,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨42,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨43,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨44,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨45,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨46,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨47,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨48,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨49,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨50,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨51,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13148) (by norm_num)
        (q := 1 - (cell13148 ⟨52,by decide⟩).lower)
        (by norm_num [cell13148]) (by norm_num [cell13148])
      exact ⟨E.1,E.2.trans (by norm_num [cell13148])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13148

/-! Source-cell containment and simple scalar guards at 13148. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13148)
open BstLean.Part268 (cell13148)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13148 ⟨10,by decide⟩).lower ∧ (cell13148 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13148 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13148 ⟨11,by decide⟩).lower ∧ (cell13148 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13148 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13148 ⟨12,by decide⟩).lower ∧ (cell13148 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13148 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13148 ⟨13,by decide⟩).lower ∧ (cell13148 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13148 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13148 ⟨14,by decide⟩).lower ∧ (cell13148 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13148 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13148 ⟨15,by decide⟩).lower ∧ (cell13148 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13148 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13148 ⟨16,by decide⟩).lower ∧ (cell13148 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13148 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13148 ⟨17,by decide⟩).lower ∧ (cell13148 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13148 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13148 ⟨18,by decide⟩).lower ∧ (cell13148 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13148 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13148 ⟨19,by decide⟩).lower ∧ (cell13148 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13148 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13148 ⟨20,by decide⟩).lower ∧ (cell13148 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13148 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13148 ⟨21,by decide⟩).lower ∧ (cell13148 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13148 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13148 ⟨22,by decide⟩).lower ∧ (cell13148 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13148 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13148 ⟨23,by decide⟩).lower ∧ (cell13148 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13148 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13148 ⟨24,by decide⟩).lower ∧ (cell13148 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13148 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13148 ⟨25,by decide⟩).lower ∧ (cell13148 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13148 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13148 ⟨26,by decide⟩).lower ∧ (cell13148 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13148 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13148 ⟨27,by decide⟩).lower ∧ (cell13148 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13148 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13148 ⟨28,by decide⟩).lower ∧ (cell13148 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13148 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13148 ⟨29,by decide⟩).lower ∧ (cell13148 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13148 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13148 ⟨30,by decide⟩).lower ∧ (cell13148 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13148 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13148 ⟨31,by decide⟩).lower ∧ (cell13148 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13148 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13148 ⟨32,by decide⟩).lower ∧ (cell13148 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13148 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13148 ⟨33,by decide⟩).lower ∧ (cell13148 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13148 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13148 ⟨34,by decide⟩).lower ∧ (cell13148 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13148 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13148 ⟨35,by decide⟩).lower ∧ (cell13148 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13148 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13148 ⟨36,by decide⟩).lower ∧ (cell13148 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13148 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13148 ⟨37,by decide⟩).lower ∧ (cell13148 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13148 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13148 ⟨38,by decide⟩).lower ∧ (cell13148 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13148 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13148 ⟨39,by decide⟩).lower ∧ (cell13148 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13148 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13148 ⟨40,by decide⟩).lower ∧ (cell13148 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13148 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13148 ⟨41,by decide⟩).lower ∧ (cell13148 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13148 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13148 ⟨42,by decide⟩).lower ∧ (cell13148 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13148 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13148 ⟨43,by decide⟩).lower ∧ (cell13148 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13148 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13148 ⟨44,by decide⟩).lower ∧ (cell13148 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13148 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13148 ⟨45,by decide⟩).lower ∧ (cell13148 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13148 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13148 ⟨46,by decide⟩).lower ∧ (cell13148 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13148 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13148 ⟨47,by decide⟩).lower ∧ (cell13148 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13148 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13148 ⟨48,by decide⟩).lower ∧ (cell13148 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13148 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13148 ⟨49,by decide⟩).lower ∧ (cell13148 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13148 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13148 ⟨50,by decide⟩).lower ∧ (cell13148 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13148 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13148 ⟨51,by decide⟩).lower ∧ (cell13148 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13148 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13148 ⟨52,by decide⟩).lower ∧ (cell13148 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13148 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13148 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13148 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13148,cell13148,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13148 i).lower ∧
    (cell13148 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13148 i).upper ≤ (0.532 : ℝ) ∧
    (cell13148 i).centre ≤ (0.1 : ℝ) ∧ (cell13148 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13148 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13148 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13148

/-! The local source numeric instances at 13148 have no network premises. -/
namespace BstLean.Part269.N13148
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13148)
open BstLean.Part268 (cell13148)

noncomputable def sourceNumerics13148 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13148 (cell13148 i)
      scalarRow13148.M scalarRow13148.H scalarRow13148.xi := by
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
    energy_allowance := scalarRow13148.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13148]
    centre_nonneg := (scalarRow13148.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13148])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13148
/-! Actual 13149 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13149 ≤ (1.035187189634 : ℝ) := by
  have hr : (114.669089121698 : ℝ) ≤ √(13149 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.669089121698 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13149 13149 (11 / 1000) ≤
    (0.008336046889 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13149) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.669089121698 : ℝ) ≤ √(13149 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13149)
  have hdiv : K / √(13149 : ℝ) ≤ K / 114.669089121698 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.669089121698 ≤ (0.008336046889 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13149.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13149 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13149 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13149 := gPlus_lower 13149
end BstLean.Part269.N13149

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13149
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035187189633 : ℝ) ≤ wn 13149 := by
  have hn : √(13149 : ℝ) ≤ 114.669089121699 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13149 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.669089121699 ≤ 2 / √(13149 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243133776 : ℝ) ≤ rhoBar 13149 BstLean.Part154.csC ∧
    rhoBar 13149 BstLean.Part154.csC ≤ 0.000243134152 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035187189633 : ℝ) / (1.295212 * 13149) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035187189634 : ℝ) / (1.29521 * 13149) := by gcongr
      _ ≤ (0.000243134152 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13149 BstLean.Part154.csC) ≤ 0.000972595723 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13149 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) ≤ 0.000185707206 ∧
    cc1 (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) ≤ 0.000118166790 ∧
    cc2 (rhoBar 13149 BstLean.Part154.csC) ≤ 0.000068596802 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13149 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13149 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13149 BstLean.Part154.csC * nuR (rhoBar 13149 BstLean.Part154.csC)) ≤ 0.000486283083 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243134152 : ℝ) * 0.000972595723 := by gcongr
      _ ≤ (0.000486283083 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13149 BstLean.Part154.csC) * nuR (rhoBar 13149 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972595723 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13149 BstLean.Part154.csC) * rhoBar 13149 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243134152 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243134152 / 2 + 0.399 * 0.000972595723 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185707206 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486283083 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118166790 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243134152 / 1.414213562 := by gcongr
      _ ≤ (0.000068596802 : ℝ) := by norm_num

end BstLean.Part269.N13149

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13149
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) ≤ 1.48934E-7 := by
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13149 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13149 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13149 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185707206 : ℝ) ^ 2 + 0.000118166790 ^ 2 + 3 * 0.000068596802 ^ 2 +
        2 * 0.797885 * 0.000185707206 * 0.000118166790 + 2 * 0.000185707206 * 0.000068596802 +
        4 * 0.797885 * 0.000118166790 * 0.000068596802 := by gcongr
    _ ≤ (1.48934E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13149 BstLean.Part154.csC Θ ≤ 0.002536456620 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13149 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13149 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13149 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035187189634 * 1.48934E-7 / (0.000243133776 : ℝ) := by gcongr
    _ ≤ 0.002536456620 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13149 BstLean.Part154.csC Θ ≤ 0.002812639971 + 0.000640921825 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13149 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13149 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035187189634 : ℝ) * ((2 * Θ * 0.000243134152 +
        (6863 / 10000) * 0.000243134152 * 13149 * 0.000972595723) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002812639971 + 0.000640921825 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13149 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13149 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13149 0.011 Θ ∧ gammaRatio 13149 0.011 Θ ≤ 0.000083583235 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13149 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035187189634 : ℝ) * 0.525 / ((1 - 0.011) * 13149) := by gcongr
      _ ≤ (0.000083583235 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13149 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13149 0.011 Θ) :=
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
    badAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13149 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13149 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13149 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13149 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13149 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13149 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13149 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13149 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13149 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13149 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035187189634 : ℝ) * 13149 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003161728457 + 0.003177378445 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13149

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13149
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13149 BstLean.Part154.csC) (piBar (rhoBar 13149 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13149 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13149 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13149 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13149 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13149 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13149 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13149 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13149 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13149 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13149 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051570804132 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13149) ≤ 0.010414642606 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13149 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035187189634)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010414642606 + 2 * 0.737676 / 13149) := by gcongr
    _ ≤ (0.051570804132 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13149 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13149

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13149
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523180044 : ℝ) ≤ plow 13149 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13149) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336452141)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331639726) : eMP 13149 0.011 xi bn ≤ 0.001147011052 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13149 : ℝ) * (1 - 0.011))) ≤ 0.000567183807 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331639726 / (13149 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567183807 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567183807 : ℝ) + 3.141593 * 0.052336452141 / (13149 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001147011052 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336452141)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331639726) : PiBarMP 13149 12 0.011 xi bn ≤ 0.158446989989 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13149 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036491639125 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.036665156431 : ℝ) ≤ √((13149 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.669089121698 : ℝ) ≤ √(13149 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13149) ≤ 0.121500993594 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036491639125 + 0.052336452141 * 1.772454 / (2 * (114.036665156431 : ℝ))) * (1 + 0.001147011052) +
        8 / (13149 * 114.669089121698) + 0.121500993594 := by gcongr
    _ ≤ (0.158446989989 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336452141)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331639726) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280342419813) :
    parallelOracle 13149 0.011 xi bn cd ≤ 0.159403908641 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13149 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13149 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523180044 : ℝ) ≤ plow 13149 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.669089121698 : ℝ) ≤ √(13149 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280342419813 : ℝ) / (2 * 0.560523180044 * 114.669089121698)) * 0.158446989989 +
        0.280342419813 ^ 2 / (2 * 0.560523180044 * 114.669089121698) := by gcongr
    _ ≤ (0.159403908641 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052336452141) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331639726)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280342419813) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13149 13149 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523180044 : ℝ) ≤ plow 13149 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.669089121698 : ℝ) ≤ √(13149 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13149 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13149 Θ 1.22 ≤ 0.011564585628 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.669089121698 := by gcongr <;> linarith
      _ ≤ (0.011564585628 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13149 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13149 13149 0.011 ≤ 0.008336046889 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13149 13149 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13149 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13149 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13149 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13149 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159403908641 + 0.011564585628 + (0.008336046889 : ℝ) *
        (1 + 2 * (0.280342419813 + 0.011564585628) / (0.560523180044 * 114.669089121698))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13149]

end BstLean.Part269.N13149

/-! The original eight local profiles supply actual 13149 moment certificates. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13149 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052336452141 ∧
    0 ≤ bN 13149 BstLean.Part154.csC (groupTheta g) ∧ bN 13149 BstLean.Part154.csC (groupTheta g) ≤ 0.001331639726 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13149 13149 0.011
      (momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13149 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13149 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13149 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228771615681 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13149 0.011
      (momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13149 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13149
/-! The actual computed-centre upper energy formula at 13149. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13149

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13149)
open BstLean.Part268 (cell13149)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084278512894
  | 2 => 0.085202333922
  | 3 => 0.086121652023
  | 4 => 0.087037263066
  | 5 => 0.087950147272
  | 6 => 0.088861498739
  | 7 => 0.089772758139
  | 8 => 0.090685648733
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13149 13149 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13149 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13149

/-! Actual upper energy certificates on all 43 source endpoints at 13149. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13149)
open BstLean.Part268 (cell13149)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13149 (gMinus 13149) (1 - (cell13149 i).lower) ≤ 1 ∧
    energyUpper 13149 (gMinus 13149) (BstLean.Part211.gPlus 13149)
      (finiteEnergy 13149 13149 0.011) (1 - (cell13149 i).lower) ≤
      (cell13149 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨10,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨11,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨12,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨13,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨14,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨15,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨16,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨17,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨18,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨19,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨20,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨21,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨22,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨23,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨24,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨25,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨26,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨27,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨28,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨29,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨30,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨31,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨32,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨33,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨34,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨35,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨36,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨37,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨38,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨39,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨40,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨41,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨42,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨43,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨44,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨45,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨46,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨47,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨48,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨49,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨50,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨51,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13149) (by norm_num)
        (q := 1 - (cell13149 ⟨52,by decide⟩).lower)
        (by norm_num [cell13149]) (by norm_num [cell13149])
      exact ⟨E.1,E.2.trans (by norm_num [cell13149])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13149

/-! Source-cell containment and simple scalar guards at 13149. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13149)
open BstLean.Part268 (cell13149)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13149 ⟨10,by decide⟩).lower ∧ (cell13149 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13149 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13149 ⟨11,by decide⟩).lower ∧ (cell13149 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13149 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13149 ⟨12,by decide⟩).lower ∧ (cell13149 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13149 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13149 ⟨13,by decide⟩).lower ∧ (cell13149 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13149 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13149 ⟨14,by decide⟩).lower ∧ (cell13149 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13149 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13149 ⟨15,by decide⟩).lower ∧ (cell13149 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13149 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13149 ⟨16,by decide⟩).lower ∧ (cell13149 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13149 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13149 ⟨17,by decide⟩).lower ∧ (cell13149 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13149 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13149 ⟨18,by decide⟩).lower ∧ (cell13149 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13149 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13149 ⟨19,by decide⟩).lower ∧ (cell13149 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13149 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13149 ⟨20,by decide⟩).lower ∧ (cell13149 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13149 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13149 ⟨21,by decide⟩).lower ∧ (cell13149 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13149 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13149 ⟨22,by decide⟩).lower ∧ (cell13149 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13149 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13149 ⟨23,by decide⟩).lower ∧ (cell13149 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13149 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13149 ⟨24,by decide⟩).lower ∧ (cell13149 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13149 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13149 ⟨25,by decide⟩).lower ∧ (cell13149 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13149 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13149 ⟨26,by decide⟩).lower ∧ (cell13149 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13149 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13149 ⟨27,by decide⟩).lower ∧ (cell13149 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13149 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13149 ⟨28,by decide⟩).lower ∧ (cell13149 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13149 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13149 ⟨29,by decide⟩).lower ∧ (cell13149 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13149 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13149 ⟨30,by decide⟩).lower ∧ (cell13149 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13149 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13149 ⟨31,by decide⟩).lower ∧ (cell13149 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13149 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13149 ⟨32,by decide⟩).lower ∧ (cell13149 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13149 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13149 ⟨33,by decide⟩).lower ∧ (cell13149 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13149 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13149 ⟨34,by decide⟩).lower ∧ (cell13149 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13149 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13149 ⟨35,by decide⟩).lower ∧ (cell13149 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13149 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13149 ⟨36,by decide⟩).lower ∧ (cell13149 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13149 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13149 ⟨37,by decide⟩).lower ∧ (cell13149 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13149 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13149 ⟨38,by decide⟩).lower ∧ (cell13149 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13149 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13149 ⟨39,by decide⟩).lower ∧ (cell13149 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13149 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13149 ⟨40,by decide⟩).lower ∧ (cell13149 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13149 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13149 ⟨41,by decide⟩).lower ∧ (cell13149 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13149 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13149 ⟨42,by decide⟩).lower ∧ (cell13149 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13149 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13149 ⟨43,by decide⟩).lower ∧ (cell13149 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13149 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13149 ⟨44,by decide⟩).lower ∧ (cell13149 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13149 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13149 ⟨45,by decide⟩).lower ∧ (cell13149 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13149 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13149 ⟨46,by decide⟩).lower ∧ (cell13149 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13149 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13149 ⟨47,by decide⟩).lower ∧ (cell13149 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13149 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13149 ⟨48,by decide⟩).lower ∧ (cell13149 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13149 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13149 ⟨49,by decide⟩).lower ∧ (cell13149 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13149 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13149 ⟨50,by decide⟩).lower ∧ (cell13149 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13149 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13149 ⟨51,by decide⟩).lower ∧ (cell13149 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13149 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13149 ⟨52,by decide⟩).lower ∧ (cell13149 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13149 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13149 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13149 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13149,cell13149,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13149 i).lower ∧
    (cell13149 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13149 i).upper ≤ (0.532 : ℝ) ∧
    (cell13149 i).centre ≤ (0.1 : ℝ) ∧ (cell13149 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13149 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13149 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13149

/-! The local source numeric instances at 13149 have no network premises. -/
namespace BstLean.Part269.N13149
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13149)
open BstLean.Part268 (cell13149)

noncomputable def sourceNumerics13149 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13149 (cell13149 i)
      scalarRow13149.M scalarRow13149.H scalarRow13149.xi := by
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
    energy_allowance := scalarRow13149.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13149]
    centre_nonneg := (scalarRow13149.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13149])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13149