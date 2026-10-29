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
import BstLean.Part269Direction11
import BstLean.Part269Shared11
import BstLean.Part269Finite
import BstLean.Part269Rows11
import BstLean.Part269Source
/-! Actual 12638 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12638 ≤ (1.035897724206 : ℝ) := by
  have hr : (112.418859627733 : ℝ) ≤ √(12638 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.418859627733 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12638 12638 (11 / 1000) ≤
    (0.008502906455 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12638) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.418859627733 : ℝ) ≤ √(12638 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12638)
  have hdiv : K / √(12638 : ℝ) ≤ K / 112.418859627733 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.418859627733 ≤ (0.008502906455 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12638.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12638 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12638 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12638 := gPlus_lower 12638
end BstLean.Part269.N12638

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12638
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035897724205 : ℝ) ≤ wn 12638 := by
  have hn : √(12638 : ℝ) ≤ 112.418859627734 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12638 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.418859627734 ≤ 2 / √(12638 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253138183 : ℝ) ≤ rhoBar 12638 BstLean.Part154.csC ∧
    rhoBar 12638 BstLean.Part154.csC ≤ 0.000253138575 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035897724205 : ℝ) / (1.295212 * 12638) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035897724206 : ℝ) / (1.29521 * 12638) := by gcongr
      _ ≤ (0.000253138575 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12638 BstLean.Part154.csC) ≤ 0.001012618380 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12638 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) ≤ 0.000193348996 ∧
    cc1 (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) ≤ 0.000123029241 ∧
    cc2 (rhoBar 12638 BstLean.Part154.csC) ≤ 0.000071419406 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12638 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12638 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12638 BstLean.Part154.csC * nuR (rhoBar 12638 BstLean.Part154.csC)) ≤ 0.000506293170 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253138575 : ℝ) * 0.001012618380 := by gcongr
      _ ≤ (0.000506293170 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12638 BstLean.Part154.csC) * nuR (rhoBar 12638 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012618380 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12638 BstLean.Part154.csC) * rhoBar 12638 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253138575 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253138575 / 2 + 0.399 * 0.001012618380 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193348996 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506293170 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123029241 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253138575 / 1.414213562 := by gcongr
      _ ≤ (0.000071419406 : ℝ) := by norm_num

end BstLean.Part269.N12638

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12638
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) ≤ 1.61443E-7 := by
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12638 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12638 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12638 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193348996 : ℝ) ^ 2 + 0.000123029241 ^ 2 + 3 * 0.000071419406 ^ 2 +
        2 * 0.797885 * 0.000193348996 * 0.000123029241 + 2 * 0.000193348996 * 0.000071419406 +
        4 * 0.797885 * 0.000123029241 * 0.000071419406 := by gcongr
    _ ≤ (1.61443E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12638 BstLean.Part154.csC Θ ≤ 0.002642642597 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12638 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12638 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12638 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035897724206 * 1.61443E-7 / (0.000253138183 : ℝ) := by gcongr
    _ ≤ 0.002642642597 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12638 BstLean.Part154.csC Θ ≤ 0.002932402458 + 0.000667752334 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12638 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12638 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035897724206 : ℝ) * ((2 * Θ * 0.000253138575 +
        (6863 / 10000) * 0.000253138575 * 12638 * 0.001012618380) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002932402458 + 0.000667752334 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12638 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12638 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12638 0.011 Θ ∧ gammaRatio 12638 0.011 Θ ≤ 0.000087022496 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12638 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035897724206 : ℝ) * 0.525 / ((1 - 0.011) * 12638) := by gcongr
      _ ≤ (0.000087022496 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12638 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12638 0.011 Θ) :=
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
    badAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12638 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12638 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12638 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12638 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12638 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12638 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12638 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12638 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12638 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12638 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035897724206 : ℝ) * 12638 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003609108929 + 0.003310394931 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12638

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12638
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12638 BstLean.Part154.csC) (piBar (rhoBar 12638 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12638 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12638 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12638 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12638 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12638 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12638 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12638 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12638 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12638 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12638 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052614292793 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12638) ≤ 0.010623107058 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12638 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035897724206)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010623107058 + 2 * 0.737676 / 12638) := by gcongr
    _ ≤ (0.052614292793 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12638 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12638

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12638
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500750712 : ℝ) ≤ plow 12638 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12638) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853666268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387387364) : eMP 12638 0.011 xi bn ≤ 0.001194329815 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12638 : ℝ) * (1 - 0.011))) ≤ 0.000590522578 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387387364 / (12638 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590522578 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590522578 : ℝ) + 3.141593 * 0.052853666268 / (12638 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194329815 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853666268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387387364) : PiBarMP 12638 12 0.011 xi bn ≤ 0.161650251570 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12638 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037247649108 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.798846147891 : ℝ) ≤ √((12638 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.418859627733 : ℝ) ≤ √(12638 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12638) ≤ 0.123933015412 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037247649108 + 0.052853666268 * 1.772454 / (2 * (111.798846147891 : ℝ))) * (1 + 0.001194329815) +
        8 / (12638 * 112.418859627733) + 0.123933015412 := by gcongr
    _ ≤ (0.161650251570 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853666268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387387364) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282513545224) :
    parallelOracle 12638 0.011 xi bn cd ≤ 0.162645971185 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12638 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12638 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500750712 : ℝ) ≤ plow 12638 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.418859627733 : ℝ) ≤ √(12638 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282513545224 : ℝ) / (2 * 0.560500750712 * 112.418859627733)) * 0.161650251570 +
        0.282513545224 ^ 2 / (2 * 0.560500750712 * 112.418859627733) := by gcongr
    _ ≤ (0.162645971185 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853666268) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387387364)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282513545224) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12638 12638 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500750712 : ℝ) ≤ plow 12638 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.418859627733 : ℝ) ≤ √(12638 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12638 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12638 Θ 1.22 ≤ 0.011796067888 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.418859627733 := by gcongr <;> linarith
      _ ≤ (0.011796067888 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12638 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12638 12638 0.011 ≤ 0.008502906455 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12638 12638 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12638 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12638 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12638 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12638 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162645971185 + 0.011796067888 + (0.008502906455 : ℝ) *
        (1 + 2 * (0.282513545224 + 0.011796067888) / (0.560500750712 * 112.418859627733))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12638]

end BstLean.Part269.N12638

/-! The original eight local profiles supply actual 12638 moment certificates. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12638 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052853666268 ∧
    0 ≤ bN 12638 BstLean.Part154.csC (groupTheta g) ∧ bN 12638 BstLean.Part154.csC (groupTheta g) ≤ 0.001387387364 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12638 12638 0.011
      (momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12638 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12638 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12638 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229899252431 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12638 0.011
      (momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12638 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12638
/-! The actual computed-centre upper energy formula at 12638. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12638

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12638)
open BstLean.Part268 (cell12638)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085673194312
  | 2 => 0.086619353298
  | 3 => 0.087564157156
  | 4 => 0.088509139769
  | 5 => 0.089456152531
  | 6 => 0.090407410989
  | 7 => 0.091365545795
  | 8 => 0.092333657959
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12638 12638 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12638 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12638

/-! Actual upper energy certificates on all 43 source endpoints at 12638. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12638)
open BstLean.Part268 (cell12638)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12638 (gMinus 12638) (1 - (cell12638 i).lower) ≤ 1 ∧
    energyUpper 12638 (gMinus 12638) (BstLean.Part211.gPlus 12638)
      (finiteEnergy 12638 12638 0.011) (1 - (cell12638 i).lower) ≤
      (cell12638 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨10,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨11,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨12,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨13,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨14,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨15,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨16,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨17,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨18,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨19,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨20,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨21,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨22,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨23,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨24,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨25,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨26,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨27,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨28,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨29,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨30,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨31,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨32,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨33,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨34,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨35,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨36,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨37,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨38,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨39,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨40,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨41,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨42,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨43,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨44,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨45,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨46,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨47,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨48,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨49,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨50,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨51,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12638) (by norm_num)
        (q := 1 - (cell12638 ⟨52,by decide⟩).lower)
        (by norm_num [cell12638]) (by norm_num [cell12638])
      exact ⟨E.1,E.2.trans (by norm_num [cell12638])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12638

/-! Source-cell containment and simple scalar guards at 12638. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12638)
open BstLean.Part268 (cell12638)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12638 ⟨10,by decide⟩).lower ∧ (cell12638 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12638 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12638 ⟨11,by decide⟩).lower ∧ (cell12638 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12638 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12638 ⟨12,by decide⟩).lower ∧ (cell12638 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12638 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12638 ⟨13,by decide⟩).lower ∧ (cell12638 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12638 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12638 ⟨14,by decide⟩).lower ∧ (cell12638 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12638 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12638 ⟨15,by decide⟩).lower ∧ (cell12638 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12638 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12638 ⟨16,by decide⟩).lower ∧ (cell12638 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12638 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12638 ⟨17,by decide⟩).lower ∧ (cell12638 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12638 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12638 ⟨18,by decide⟩).lower ∧ (cell12638 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12638 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12638 ⟨19,by decide⟩).lower ∧ (cell12638 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12638 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12638 ⟨20,by decide⟩).lower ∧ (cell12638 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12638 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12638 ⟨21,by decide⟩).lower ∧ (cell12638 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12638 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12638 ⟨22,by decide⟩).lower ∧ (cell12638 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12638 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12638 ⟨23,by decide⟩).lower ∧ (cell12638 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12638 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12638 ⟨24,by decide⟩).lower ∧ (cell12638 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12638 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12638 ⟨25,by decide⟩).lower ∧ (cell12638 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12638 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12638 ⟨26,by decide⟩).lower ∧ (cell12638 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12638 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12638 ⟨27,by decide⟩).lower ∧ (cell12638 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12638 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12638 ⟨28,by decide⟩).lower ∧ (cell12638 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12638 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12638 ⟨29,by decide⟩).lower ∧ (cell12638 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12638 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12638 ⟨30,by decide⟩).lower ∧ (cell12638 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12638 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12638 ⟨31,by decide⟩).lower ∧ (cell12638 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12638 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12638 ⟨32,by decide⟩).lower ∧ (cell12638 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12638 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12638 ⟨33,by decide⟩).lower ∧ (cell12638 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12638 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12638 ⟨34,by decide⟩).lower ∧ (cell12638 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12638 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12638 ⟨35,by decide⟩).lower ∧ (cell12638 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12638 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12638 ⟨36,by decide⟩).lower ∧ (cell12638 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12638 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12638 ⟨37,by decide⟩).lower ∧ (cell12638 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12638 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12638 ⟨38,by decide⟩).lower ∧ (cell12638 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12638 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12638 ⟨39,by decide⟩).lower ∧ (cell12638 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12638 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12638 ⟨40,by decide⟩).lower ∧ (cell12638 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12638 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12638 ⟨41,by decide⟩).lower ∧ (cell12638 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12638 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12638 ⟨42,by decide⟩).lower ∧ (cell12638 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12638 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12638 ⟨43,by decide⟩).lower ∧ (cell12638 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12638 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12638 ⟨44,by decide⟩).lower ∧ (cell12638 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12638 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12638 ⟨45,by decide⟩).lower ∧ (cell12638 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12638 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12638 ⟨46,by decide⟩).lower ∧ (cell12638 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12638 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12638 ⟨47,by decide⟩).lower ∧ (cell12638 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12638 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12638 ⟨48,by decide⟩).lower ∧ (cell12638 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12638 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12638 ⟨49,by decide⟩).lower ∧ (cell12638 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12638 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12638 ⟨50,by decide⟩).lower ∧ (cell12638 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12638 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12638 ⟨51,by decide⟩).lower ∧ (cell12638 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12638 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12638 ⟨52,by decide⟩).lower ∧ (cell12638 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12638 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12638 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12638 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12638,cell12638,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12638 i).lower ∧
    (cell12638 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12638 i).upper ≤ (0.532 : ℝ) ∧
    (cell12638 i).centre ≤ (0.1 : ℝ) ∧ (cell12638 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12638 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12638 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12638

/-! The local source numeric instances at 12638 have no network premises. -/
namespace BstLean.Part269.N12638
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12638)
open BstLean.Part268 (cell12638)

noncomputable def sourceNumerics12638 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12638 (cell12638 i)
      scalarRow12638.M scalarRow12638.H scalarRow12638.xi := by
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
    energy_allowance := scalarRow12638.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12638]
    centre_nonneg := (scalarRow12638.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12638])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12638
/-! Actual 12639 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12639 ≤ (1.035896291540 : ℝ) := by
  have hr : (112.423307192058 : ℝ) ≤ √(12639 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.423307192058 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12639 12639 (11 / 1000) ≤
    (0.008502570070 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12639) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.423307192058 : ℝ) ≤ √(12639 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12639)
  have hdiv : K / √(12639 : ℝ) ≤ K / 112.423307192058 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.423307192058 ≤ (0.008502570070 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12639.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12639 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12639 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12639 := gPlus_lower 12639
end BstLean.Part269.N12639

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12639
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035896291539 : ℝ) ≤ wn 12639 := by
  have hn : √(12639 : ℝ) ≤ 112.423307192059 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12639 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.423307192059 ≤ 2 / √(12639 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253117805 : ℝ) ≤ rhoBar 12639 BstLean.Part154.csC ∧
    rhoBar 12639 BstLean.Part154.csC ≤ 0.000253118197 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035896291539 : ℝ) / (1.295212 * 12639) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035896291540 : ℝ) / (1.29521 * 12639) := by gcongr
      _ ≤ (0.000253118197 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12639 BstLean.Part154.csC) ≤ 0.001012536857 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12639 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) ≤ 0.000193333431 ∧
    cc1 (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) ≤ 0.000123019336 ∧
    cc2 (rhoBar 12639 BstLean.Part154.csC) ≤ 0.000071413656 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12639 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12639 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12639 BstLean.Part154.csC * nuR (rhoBar 12639 BstLean.Part154.csC)) ≤ 0.000506252411 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253118197 : ℝ) * 0.001012536857 := by gcongr
      _ ≤ (0.000506252411 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12639 BstLean.Part154.csC) * nuR (rhoBar 12639 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012536857 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12639 BstLean.Part154.csC) * rhoBar 12639 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253118197 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253118197 / 2 + 0.399 * 0.001012536857 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193333431 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506252411 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123019336 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253118197 / 1.414213562 := by gcongr
      _ ≤ (0.000071413656 : ℝ) := by norm_num

end BstLean.Part269.N12639

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12639
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) ≤ 1.61417E-7 := by
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12639 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12639 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12639 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193333431 : ℝ) ^ 2 + 0.000123019336 ^ 2 + 3 * 0.000071413656 ^ 2 +
        2 * 0.797885 * 0.000193333431 * 0.000123019336 + 2 * 0.000193333431 * 0.000071413656 +
        4 * 0.797885 * 0.000123019336 * 0.000071413656 := by gcongr
    _ ≤ (1.61417E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12639 BstLean.Part154.csC Θ ≤ 0.002642426071 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12639 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12639 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12639 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035896291540 * 1.61417E-7 / (0.000253117805 : ℝ) := by gcongr
    _ ≤ 0.002642426071 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12639 BstLean.Part154.csC Θ ≤ 0.002932158274 + 0.000667697656 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12639 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12639 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035896291540 : ℝ) * ((2 * Θ * 0.000253118197 +
        (6863 / 10000) * 0.000253118197 * 12639 * 0.001012536857) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002932158274 + 0.000667697656 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12639 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12639 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12639 0.011 Θ ∧ gammaRatio 12639 0.011 Θ ≤ 0.000087015491 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12639 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035896291540 : ℝ) * 0.525 / ((1 - 0.011) * 12639) := by gcongr
      _ ≤ (0.000087015491 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12639 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12639 0.011 Θ) :=
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
    badAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12639 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12639 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12639 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12639 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12639 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12639 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12639 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12639 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12639 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12639 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035896291540 : ℝ) * 12639 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003608864745 + 0.003310123727 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12639

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12639
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12639 BstLean.Part154.csC) (piBar (rhoBar 12639 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12639 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12639 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12639 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12639 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12639 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12639 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12639 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12639 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12639 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12639 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052612188699 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12639) ≤ 0.010622686798 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12639 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035896291540)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010622686798 + 2 * 0.737676 / 12639) := by gcongr
    _ ≤ (0.052612188699 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12639 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12639

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12639
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500796376 : ℝ) ≤ plow 12639 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12639) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853279702)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387273688) : eMP 12639 0.011 xi bn ≤ 0.001194233559 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12639 : ℝ) * (1 - 0.011))) ≤ 0.000590475024 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387273688 / (12639 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590475024 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590475024 : ℝ) + 3.141593 * 0.052853279702 / (12639 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194233559 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853279702)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387273688) : PiBarMP 12639 12 0.011 xi bn ≤ 0.161643796912 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12639 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037246123128 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.803269182971 : ℝ) ≤ √((12639 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.423307192058 : ℝ) ≤ √(12639 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12639) ≤ 0.123928112513 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037246123128 + 0.052853279702 * 1.772454 / (2 * (111.803269182971 : ℝ))) * (1 + 0.001194233559) +
        8 / (12639 * 112.423307192058) + 0.123928112513 := by gcongr
    _ ≤ (0.161643796912 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853279702)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387273688) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282510600399) :
    parallelOracle 12639 0.011 xi bn cd ≤ 0.162639445605 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12639 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12639 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500796376 : ℝ) ≤ plow 12639 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.423307192058 : ℝ) ≤ √(12639 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282510600399 : ℝ) / (2 * 0.560500796376 * 112.423307192058)) * 0.161643796912 +
        0.282510600399 ^ 2 / (2 * 0.560500796376 * 112.423307192058) := by gcongr
    _ ≤ (0.162639445605 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052853279702) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387273688)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282510600399) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12639 12639 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500796376 : ℝ) ≤ plow 12639 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.423307192058 : ℝ) ≤ √(12639 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12639 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12639 Θ 1.22 ≤ 0.011795601225 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.423307192058 := by gcongr <;> linarith
      _ ≤ (0.011795601225 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12639 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12639 12639 0.011 ≤ 0.008502570070 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12639 12639 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12639 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12639 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12639 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12639 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162639445605 + 0.011795601225 + (0.008502570070 : ℝ) *
        (1 + 2 * (0.282510600399 + 0.011795601225) / (0.560500796376 * 112.423307192058))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12639]

end BstLean.Part269.N12639

/-! The original eight local profiles supply actual 12639 moment certificates. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12639 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052853279702 ∧
    0 ≤ bN 12639 BstLean.Part154.csC (groupTheta g) ∧ bN 12639 BstLean.Part154.csC (groupTheta g) ≤ 0.001387273688 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12639 12639 0.011
      (momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12639 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12639 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12639 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229898411700 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12639 0.011
      (momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12639 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12639
/-! The actual computed-centre upper energy formula at 12639. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12639

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12639)
open BstLean.Part268 (cell12639)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085670209222
  | 2 => 0.086616311781
  | 3 => 0.087561050727
  | 4 => 0.088505958007
  | 5 => 0.089452882739
  | 6 => 0.090404037818
  | 7 => 0.091362050814
  | 8 => 0.092330019193
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12639 12639 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12639 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12639

/-! Actual upper energy certificates on all 43 source endpoints at 12639. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12639)
open BstLean.Part268 (cell12639)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12639 (gMinus 12639) (1 - (cell12639 i).lower) ≤ 1 ∧
    energyUpper 12639 (gMinus 12639) (BstLean.Part211.gPlus 12639)
      (finiteEnergy 12639 12639 0.011) (1 - (cell12639 i).lower) ≤
      (cell12639 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨10,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨11,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨12,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨13,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨14,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨15,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨16,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨17,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨18,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨19,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨20,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨21,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨22,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨23,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨24,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨25,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨26,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨27,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨28,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨29,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨30,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨31,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨32,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨33,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨34,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨35,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨36,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨37,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨38,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨39,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨40,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨41,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨42,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨43,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨44,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨45,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨46,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨47,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨48,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨49,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨50,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨51,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12639) (by norm_num)
        (q := 1 - (cell12639 ⟨52,by decide⟩).lower)
        (by norm_num [cell12639]) (by norm_num [cell12639])
      exact ⟨E.1,E.2.trans (by norm_num [cell12639])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12639

/-! Source-cell containment and simple scalar guards at 12639. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12639)
open BstLean.Part268 (cell12639)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12639 ⟨10,by decide⟩).lower ∧ (cell12639 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12639 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12639 ⟨11,by decide⟩).lower ∧ (cell12639 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12639 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12639 ⟨12,by decide⟩).lower ∧ (cell12639 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12639 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12639 ⟨13,by decide⟩).lower ∧ (cell12639 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12639 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12639 ⟨14,by decide⟩).lower ∧ (cell12639 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12639 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12639 ⟨15,by decide⟩).lower ∧ (cell12639 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12639 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12639 ⟨16,by decide⟩).lower ∧ (cell12639 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12639 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12639 ⟨17,by decide⟩).lower ∧ (cell12639 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12639 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12639 ⟨18,by decide⟩).lower ∧ (cell12639 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12639 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12639 ⟨19,by decide⟩).lower ∧ (cell12639 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12639 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12639 ⟨20,by decide⟩).lower ∧ (cell12639 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12639 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12639 ⟨21,by decide⟩).lower ∧ (cell12639 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12639 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12639 ⟨22,by decide⟩).lower ∧ (cell12639 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12639 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12639 ⟨23,by decide⟩).lower ∧ (cell12639 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12639 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12639 ⟨24,by decide⟩).lower ∧ (cell12639 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12639 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12639 ⟨25,by decide⟩).lower ∧ (cell12639 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12639 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12639 ⟨26,by decide⟩).lower ∧ (cell12639 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12639 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12639 ⟨27,by decide⟩).lower ∧ (cell12639 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12639 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12639 ⟨28,by decide⟩).lower ∧ (cell12639 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12639 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12639 ⟨29,by decide⟩).lower ∧ (cell12639 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12639 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12639 ⟨30,by decide⟩).lower ∧ (cell12639 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12639 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12639 ⟨31,by decide⟩).lower ∧ (cell12639 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12639 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12639 ⟨32,by decide⟩).lower ∧ (cell12639 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12639 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12639 ⟨33,by decide⟩).lower ∧ (cell12639 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12639 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12639 ⟨34,by decide⟩).lower ∧ (cell12639 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12639 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12639 ⟨35,by decide⟩).lower ∧ (cell12639 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12639 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12639 ⟨36,by decide⟩).lower ∧ (cell12639 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12639 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12639 ⟨37,by decide⟩).lower ∧ (cell12639 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12639 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12639 ⟨38,by decide⟩).lower ∧ (cell12639 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12639 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12639 ⟨39,by decide⟩).lower ∧ (cell12639 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12639 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12639 ⟨40,by decide⟩).lower ∧ (cell12639 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12639 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12639 ⟨41,by decide⟩).lower ∧ (cell12639 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12639 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12639 ⟨42,by decide⟩).lower ∧ (cell12639 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12639 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12639 ⟨43,by decide⟩).lower ∧ (cell12639 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12639 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12639 ⟨44,by decide⟩).lower ∧ (cell12639 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12639 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12639 ⟨45,by decide⟩).lower ∧ (cell12639 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12639 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12639 ⟨46,by decide⟩).lower ∧ (cell12639 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12639 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12639 ⟨47,by decide⟩).lower ∧ (cell12639 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12639 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12639 ⟨48,by decide⟩).lower ∧ (cell12639 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12639 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12639 ⟨49,by decide⟩).lower ∧ (cell12639 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12639 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12639 ⟨50,by decide⟩).lower ∧ (cell12639 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12639 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12639 ⟨51,by decide⟩).lower ∧ (cell12639 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12639 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12639 ⟨52,by decide⟩).lower ∧ (cell12639 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12639 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12639 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12639 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12639,cell12639,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12639 i).lower ∧
    (cell12639 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12639 i).upper ≤ (0.532 : ℝ) ∧
    (cell12639 i).centre ≤ (0.1 : ℝ) ∧ (cell12639 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12639 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12639 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12639

/-! The local source numeric instances at 12639 have no network premises. -/
namespace BstLean.Part269.N12639
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12639)
open BstLean.Part268 (cell12639)

noncomputable def sourceNumerics12639 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12639 (cell12639 i)
      scalarRow12639.M scalarRow12639.H scalarRow12639.xi := by
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
    energy_allowance := scalarRow12639.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12639]
    centre_nonneg := (scalarRow12639.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12639])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12639
/-! Actual 12640 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12640 ≤ (1.035894859045 : ℝ) := by
  have hr : (112.427754580441 : ℝ) ≤ √(12640 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.427754580441 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12640 12640 (11 / 1000) ≤
    (0.008502233725 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12640) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.427754580441 : ℝ) ≤ √(12640 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12640)
  have hdiv : K / √(12640 : ℝ) ≤ K / 112.427754580441 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.427754580441 ≤ (0.008502233725 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12640.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12640 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12640 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12640 := gPlus_lower 12640
end BstLean.Part269.N12640

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12640
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035894859044 : ℝ) ≤ wn 12640 := by
  have hn : √(12640 : ℝ) ≤ 112.427754580442 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12640 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.427754580442 ≤ 2 / √(12640 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253097430 : ℝ) ≤ rhoBar 12640 BstLean.Part154.csC ∧
    rhoBar 12640 BstLean.Part154.csC ≤ 0.000253097822 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035894859044 : ℝ) / (1.295212 * 12640) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035894859045 : ℝ) / (1.29521 * 12640) := by gcongr
      _ ≤ (0.000253097822 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12640 BstLean.Part154.csC) ≤ 0.001012455347 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12640 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) ≤ 0.000193317867 ∧
    cc1 (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) ≤ 0.000123009434 ∧
    cc2 (rhoBar 12640 BstLean.Part154.csC) ≤ 0.000071407908 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12640 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12640 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12640 BstLean.Part154.csC * nuR (rhoBar 12640 BstLean.Part154.csC)) ≤ 0.000506211659 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253097822 : ℝ) * 0.001012455347 := by gcongr
      _ ≤ (0.000506211659 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12640 BstLean.Part154.csC) * nuR (rhoBar 12640 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012455347 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12640 BstLean.Part154.csC) * rhoBar 12640 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253097822 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253097822 / 2 + 0.399 * 0.001012455347 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193317867 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506211659 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123009434 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253097822 / 1.414213562 := by gcongr
      _ ≤ (0.000071407908 : ℝ) := by norm_num

end BstLean.Part269.N12640

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12640
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) ≤ 1.61391E-7 := by
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12640 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12640 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12640 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193317867 : ℝ) ^ 2 + 0.000123009434 ^ 2 + 3 * 0.000071407908 ^ 2 +
        2 * 0.797885 * 0.000193317867 * 0.000123009434 + 2 * 0.000193317867 * 0.000071407908 +
        4 * 0.797885 * 0.000123009434 * 0.000071407908 := by gcongr
    _ ≤ (1.61391E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12640 BstLean.Part154.csC Θ ≤ 0.002642209480 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12640 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12640 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12640 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035894859045 * 1.61391E-7 / (0.000253097430 : ℝ) := by gcongr
    _ ≤ 0.002642209480 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12640 BstLean.Part154.csC Θ ≤ 0.002931914126 + 0.000667642986 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12640 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12640 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035894859045 : ℝ) * ((2 * Θ * 0.000253097822 +
        (6863 / 10000) * 0.000253097822 * 12640 * 0.001012455347) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002931914126 + 0.000667642986 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12640 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12640 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12640 0.011 Θ ∧ gammaRatio 12640 0.011 Θ ≤ 0.000087008486 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12640 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035894859045 : ℝ) * 0.525 / ((1 - 0.011) * 12640) := by gcongr
      _ ≤ (0.000087008486 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12640 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12640 0.011 Θ) :=
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
    badAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12640 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12640 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12640 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12640 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12640 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12640 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12640 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12640 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12640 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12640 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035894859045 : ℝ) * 12640 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003608620597 + 0.003309852466 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12640

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12640
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12640 BstLean.Part154.csC) (piBar (rhoBar 12640 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12640 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12640 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12640 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12640 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12640 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12640 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12640 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12640 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12640 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12640 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052610084861 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12640) ≤ 0.010622266589 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12640 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035894859045)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010622266589 + 2 * 0.737676 / 12640) := by gcongr
    _ ≤ (0.052610084861 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12640 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12640

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12640
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500842033 : ℝ) ≤ plow 12640 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12640) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852893142)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387159977) : eMP 12640 0.011 xi bn ≤ 0.001194137297 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12640 : ℝ) * (1 - 0.011))) ≤ 0.000590427467 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387159977 / (12640 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590427467 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590427467 : ℝ) + 3.141593 * 0.052852893142 / (12640 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194137297 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852893142)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387159977) : PiBarMP 12640 12 0.011 xi bn ≤ 0.161637342306 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12640 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037244596615 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.807692043079 : ℝ) ≤ √((12640 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.427754580441 : ℝ) ≤ √(12640 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12640) ≤ 0.123923210197 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037244596615 + 0.052852893142 * 1.772454 / (2 * (111.807692043079 : ℝ))) * (1 + 0.001194137297) +
        8 / (12640 * 112.427754580441) + 0.123923210197 := by gcongr
    _ ≤ (0.161637342306 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852893142)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387159977) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282507655840) :
    parallelOracle 12640 0.011 xi bn cd ≤ 0.162632920086 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12640 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12640 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500842033 : ℝ) ≤ plow 12640 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.427754580441 : ℝ) ≤ √(12640 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282507655840 : ℝ) / (2 * 0.560500842033 * 112.427754580441)) * 0.161637342306 +
        0.282507655840 ^ 2 / (2 * 0.560500842033 * 112.427754580441) := by gcongr
    _ ≤ (0.162632920086 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852893142) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387159977)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282507655840) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12640 12640 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500842033 : ℝ) ≤ plow 12640 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.427754580441 : ℝ) ≤ √(12640 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12640 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12640 Θ 1.22 ≤ 0.011795134618 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.427754580441 := by gcongr <;> linarith
      _ ≤ (0.011795134618 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12640 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12640 12640 0.011 ≤ 0.008502233725 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12640 12640 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12640 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12640 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12640 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12640 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162632920086 + 0.011795134618 + (0.008502233725 : ℝ) *
        (1 + 2 * (0.282507655840 + 0.011795134618) / (0.560500842033 * 112.427754580441))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12640]

end BstLean.Part269.N12640

/-! The original eight local profiles supply actual 12640 moment certificates. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12640 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052852893142 ∧
    0 ≤ bN 12640 BstLean.Part154.csC (groupTheta g) ∧ bN 12640 BstLean.Part154.csC (groupTheta g) ≤ 0.001387159977 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12640 12640 0.011
      (momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12640 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12640 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12640 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229897570979 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12640 0.011
      (momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12640 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12640
/-! The actual computed-centre upper energy formula at 12640. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12640

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12640)
open BstLean.Part268 (cell12640)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085667225286
  | 2 => 0.086613271467
  | 3 => 0.087557945560
  | 4 => 0.088502777580
  | 5 => 0.089449614371
  | 6 => 0.090400666178
  | 7 => 0.091358557497
  | 8 => 0.092326382247
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12640 12640 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12640 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12640

/-! Actual upper energy certificates on all 43 source endpoints at 12640. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12640)
open BstLean.Part268 (cell12640)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12640 (gMinus 12640) (1 - (cell12640 i).lower) ≤ 1 ∧
    energyUpper 12640 (gMinus 12640) (BstLean.Part211.gPlus 12640)
      (finiteEnergy 12640 12640 0.011) (1 - (cell12640 i).lower) ≤
      (cell12640 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨10,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨11,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨12,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨13,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨14,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨15,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨16,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨17,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨18,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨19,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨20,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨21,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨22,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨23,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨24,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨25,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨26,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨27,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨28,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨29,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨30,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨31,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨32,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨33,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨34,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨35,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨36,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨37,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨38,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨39,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨40,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨41,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨42,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨43,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨44,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨45,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨46,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨47,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨48,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨49,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨50,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨51,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12640) (by norm_num)
        (q := 1 - (cell12640 ⟨52,by decide⟩).lower)
        (by norm_num [cell12640]) (by norm_num [cell12640])
      exact ⟨E.1,E.2.trans (by norm_num [cell12640])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12640

/-! Source-cell containment and simple scalar guards at 12640. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12640)
open BstLean.Part268 (cell12640)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12640 ⟨10,by decide⟩).lower ∧ (cell12640 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12640 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12640 ⟨11,by decide⟩).lower ∧ (cell12640 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12640 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12640 ⟨12,by decide⟩).lower ∧ (cell12640 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12640 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12640 ⟨13,by decide⟩).lower ∧ (cell12640 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12640 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12640 ⟨14,by decide⟩).lower ∧ (cell12640 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12640 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12640 ⟨15,by decide⟩).lower ∧ (cell12640 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12640 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12640 ⟨16,by decide⟩).lower ∧ (cell12640 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12640 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12640 ⟨17,by decide⟩).lower ∧ (cell12640 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12640 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12640 ⟨18,by decide⟩).lower ∧ (cell12640 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12640 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12640 ⟨19,by decide⟩).lower ∧ (cell12640 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12640 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12640 ⟨20,by decide⟩).lower ∧ (cell12640 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12640 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12640 ⟨21,by decide⟩).lower ∧ (cell12640 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12640 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12640 ⟨22,by decide⟩).lower ∧ (cell12640 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12640 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12640 ⟨23,by decide⟩).lower ∧ (cell12640 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12640 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12640 ⟨24,by decide⟩).lower ∧ (cell12640 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12640 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12640 ⟨25,by decide⟩).lower ∧ (cell12640 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12640 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12640 ⟨26,by decide⟩).lower ∧ (cell12640 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12640 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12640 ⟨27,by decide⟩).lower ∧ (cell12640 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12640 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12640 ⟨28,by decide⟩).lower ∧ (cell12640 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12640 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12640 ⟨29,by decide⟩).lower ∧ (cell12640 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12640 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12640 ⟨30,by decide⟩).lower ∧ (cell12640 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12640 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12640 ⟨31,by decide⟩).lower ∧ (cell12640 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12640 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12640 ⟨32,by decide⟩).lower ∧ (cell12640 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12640 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12640 ⟨33,by decide⟩).lower ∧ (cell12640 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12640 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12640 ⟨34,by decide⟩).lower ∧ (cell12640 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12640 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12640 ⟨35,by decide⟩).lower ∧ (cell12640 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12640 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12640 ⟨36,by decide⟩).lower ∧ (cell12640 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12640 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12640 ⟨37,by decide⟩).lower ∧ (cell12640 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12640 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12640 ⟨38,by decide⟩).lower ∧ (cell12640 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12640 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12640 ⟨39,by decide⟩).lower ∧ (cell12640 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12640 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12640 ⟨40,by decide⟩).lower ∧ (cell12640 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12640 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12640 ⟨41,by decide⟩).lower ∧ (cell12640 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12640 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12640 ⟨42,by decide⟩).lower ∧ (cell12640 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12640 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12640 ⟨43,by decide⟩).lower ∧ (cell12640 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12640 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12640 ⟨44,by decide⟩).lower ∧ (cell12640 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12640 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12640 ⟨45,by decide⟩).lower ∧ (cell12640 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12640 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12640 ⟨46,by decide⟩).lower ∧ (cell12640 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12640 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12640 ⟨47,by decide⟩).lower ∧ (cell12640 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12640 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12640 ⟨48,by decide⟩).lower ∧ (cell12640 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12640 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12640 ⟨49,by decide⟩).lower ∧ (cell12640 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12640 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12640 ⟨50,by decide⟩).lower ∧ (cell12640 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12640 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12640 ⟨51,by decide⟩).lower ∧ (cell12640 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12640 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12640 ⟨52,by decide⟩).lower ∧ (cell12640 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12640 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12640 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12640 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12640,cell12640,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12640 i).lower ∧
    (cell12640 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12640 i).upper ≤ (0.532 : ℝ) ∧
    (cell12640 i).centre ≤ (0.1 : ℝ) ∧ (cell12640 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12640 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12640 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12640

/-! The local source numeric instances at 12640 have no network premises. -/
namespace BstLean.Part269.N12640
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12640)
open BstLean.Part268 (cell12640)

noncomputable def sourceNumerics12640 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12640 (cell12640 i)
      scalarRow12640.M scalarRow12640.H scalarRow12640.xi := by
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
    energy_allowance := scalarRow12640.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12640]
    centre_nonneg := (scalarRow12640.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12640])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12640
/-! Actual 12641 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12641 ≤ (1.035893426721 : ℝ) := by
  have hr : (112.432201792902 : ℝ) ≤ √(12641 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.432201792902 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12641 12641 (11 / 1000) ≤
    (0.008501897419 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12641) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.432201792902 : ℝ) ≤ √(12641 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12641)
  have hdiv : K / √(12641 : ℝ) ≤ K / 112.432201792902 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.432201792902 ≤ (0.008501897419 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12641.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12641 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12641 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12641 := gPlus_lower 12641
end BstLean.Part269.N12641

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12641
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035893426720 : ℝ) ≤ wn 12641 := by
  have hn : √(12641 : ℝ) ≤ 112.432201792903 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12641 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.432201792903 ≤ 2 / √(12641 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253077058 : ℝ) ≤ rhoBar 12641 BstLean.Part154.csC ∧
    rhoBar 12641 BstLean.Part154.csC ≤ 0.000253077450 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035893426720 : ℝ) / (1.295212 * 12641) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035893426721 : ℝ) / (1.29521 * 12641) := by gcongr
      _ ≤ (0.000253077450 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12641 BstLean.Part154.csC) ≤ 0.001012373849 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12641 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) ≤ 0.000193302306 ∧
    cc1 (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) ≤ 0.000122999532 ∧
    cc2 (rhoBar 12641 BstLean.Part154.csC) ≤ 0.000071402160 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12641 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12641 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12641 BstLean.Part154.csC * nuR (rhoBar 12641 BstLean.Part154.csC)) ≤ 0.000506170912 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253077450 : ℝ) * 0.001012373849 := by gcongr
      _ ≤ (0.000506170912 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12641 BstLean.Part154.csC) * nuR (rhoBar 12641 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012373849 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12641 BstLean.Part154.csC) * rhoBar 12641 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253077450 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253077450 / 2 + 0.399 * 0.001012373849 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193302306 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506170912 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122999532 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253077450 / 1.414213562 := by gcongr
      _ ≤ (0.000071402160 : ℝ) := by norm_num

end BstLean.Part269.N12641

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12641
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) ≤ 1.61365E-7 := by
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12641 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12641 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12641 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193302306 : ℝ) ^ 2 + 0.000122999532 ^ 2 + 3 * 0.000071402160 ^ 2 +
        2 * 0.797885 * 0.000193302306 * 0.000122999532 + 2 * 0.000193302306 * 0.000071402160 +
        4 * 0.797885 * 0.000122999532 * 0.000071402160 := by gcongr
    _ ≤ (1.61365E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12641 BstLean.Part154.csC Θ ≤ 0.002641992825 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12641 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12641 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12641 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035893426721 * 1.61365E-7 / (0.000253077058 : ℝ) := by gcongr
    _ ≤ 0.002641992825 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12641 BstLean.Part154.csC Θ ≤ 0.002931670012 + 0.000667588324 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12641 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12641 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035893426721 : ℝ) * ((2 * Θ * 0.000253077450 +
        (6863 / 10000) * 0.000253077450 * 12641 * 0.001012373849) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002931670012 + 0.000667588324 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12641 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12641 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12641 0.011 Θ ∧ gammaRatio 12641 0.011 Θ ≤ 0.000087001483 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12641 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035893426721 : ℝ) * 0.525 / ((1 - 0.011) * 12641) := by gcongr
      _ ≤ (0.000087001483 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12641 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12641 0.011 Θ) :=
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
    badAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12641 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12641 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12641 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12641 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12641 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12641 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12641 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12641 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12641 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12641 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035893426721 : ℝ) * 12641 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003608376483 + 0.003309581149 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12641

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12641
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12641 BstLean.Part154.csC) (piBar (rhoBar 12641 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12641 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12641 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12641 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12641 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12641 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12641 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12641 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12641 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12641 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12641 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052607981271 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12641) ≤ 0.010621846429 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12641 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035893426721)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010621846429 + 2 * 0.737676 / 12641) := by gcongr
    _ ≤ (0.052607981271 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12641 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12641

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12641
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500887682 : ℝ) ≤ plow 12641 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12641) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852506587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387046234) : eMP 12641 0.011 xi bn ≤ 0.001194041029 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12641 : ℝ) * (1 - 0.011))) ≤ 0.000590379907 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387046234 / (12641 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590379907 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590379907 : ℝ) + 3.141593 * 0.052852506587 / (12641 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194041029 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852506587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387046234) : PiBarMP 12641 12 0.011 xi bn ≤ 0.161630887792 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12641 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037243069611 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.812114728235 : ℝ) ≤ √((12641 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.432201792902 : ℝ) ≤ √(12641 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12641) ≤ 0.123918308462 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037243069611 + 0.052852506587 * 1.772454 / (2 * (111.812114728235 : ℝ))) * (1 + 0.001194041029) +
        8 / (12641 * 112.432201792902) + 0.123918308462 := by gcongr
    _ ≤ (0.161630887792 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852506587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387046234) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282504711538) :
    parallelOracle 12641 0.011 xi bn cd ≤ 0.162626394669 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12641 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12641 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500887682 : ℝ) ≤ plow 12641 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.432201792902 : ℝ) ≤ √(12641 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282504711538 : ℝ) / (2 * 0.560500887682 * 112.432201792902)) * 0.161630887792 +
        0.282504711538 ^ 2 / (2 * 0.560500887682 * 112.432201792902) := by gcongr
    _ ≤ (0.162626394669 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852506587) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387046234)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282504711538) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12641 12641 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500887682 : ℝ) ≤ plow 12641 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.432201792902 : ℝ) ≤ √(12641 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12641 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12641 Θ 1.22 ≤ 0.011794668066 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.432201792902 := by gcongr <;> linarith
      _ ≤ (0.011794668066 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12641 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12641 12641 0.011 ≤ 0.008501897419 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12641 12641 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12641 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12641 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12641 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12641 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162626394669 + 0.011794668066 + (0.008501897419 : ℝ) *
        (1 + 2 * (0.282504711538 + 0.011794668066) / (0.560500887682 * 112.432201792902))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12641]

end BstLean.Part269.N12641

/-! The original eight local profiles supply actual 12641 moment certificates. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12641 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052852506587 ∧
    0 ≤ bN 12641 BstLean.Part154.csC (groupTheta g) ∧ bN 12641 BstLean.Part154.csC (groupTheta g) ≤ 0.001387046234 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12641 12641 0.011
      (momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12641 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12641 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12641 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229896730267 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12641 0.011
      (momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12641 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12641
/-! The actual computed-centre upper energy formula at 12641. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12641

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12641)
open BstLean.Part268 (cell12641)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085664242503
  | 2 => 0.086610232353
  | 3 => 0.087554841652
  | 4 => 0.088499598485
  | 5 => 0.089446347425
  | 6 => 0.090397296069
  | 7 => 0.091355065841
  | 8 => 0.092322747121
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12641 12641 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12641 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12641

/-! Actual upper energy certificates on all 43 source endpoints at 12641. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12641)
open BstLean.Part268 (cell12641)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12641 (gMinus 12641) (1 - (cell12641 i).lower) ≤ 1 ∧
    energyUpper 12641 (gMinus 12641) (BstLean.Part211.gPlus 12641)
      (finiteEnergy 12641 12641 0.011) (1 - (cell12641 i).lower) ≤
      (cell12641 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨10,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨11,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨12,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨13,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨14,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨15,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨16,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨17,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨18,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨19,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨20,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨21,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨22,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨23,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨24,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨25,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨26,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨27,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨28,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨29,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨30,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨31,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨32,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨33,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨34,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨35,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨36,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨37,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨38,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨39,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨40,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨41,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨42,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨43,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨44,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨45,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨46,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨47,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨48,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨49,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨50,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨51,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12641) (by norm_num)
        (q := 1 - (cell12641 ⟨52,by decide⟩).lower)
        (by norm_num [cell12641]) (by norm_num [cell12641])
      exact ⟨E.1,E.2.trans (by norm_num [cell12641])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12641

/-! Source-cell containment and simple scalar guards at 12641. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12641)
open BstLean.Part268 (cell12641)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12641 ⟨10,by decide⟩).lower ∧ (cell12641 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12641 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12641 ⟨11,by decide⟩).lower ∧ (cell12641 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12641 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12641 ⟨12,by decide⟩).lower ∧ (cell12641 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12641 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12641 ⟨13,by decide⟩).lower ∧ (cell12641 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12641 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12641 ⟨14,by decide⟩).lower ∧ (cell12641 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12641 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12641 ⟨15,by decide⟩).lower ∧ (cell12641 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12641 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12641 ⟨16,by decide⟩).lower ∧ (cell12641 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12641 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12641 ⟨17,by decide⟩).lower ∧ (cell12641 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12641 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12641 ⟨18,by decide⟩).lower ∧ (cell12641 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12641 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12641 ⟨19,by decide⟩).lower ∧ (cell12641 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12641 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12641 ⟨20,by decide⟩).lower ∧ (cell12641 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12641 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12641 ⟨21,by decide⟩).lower ∧ (cell12641 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12641 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12641 ⟨22,by decide⟩).lower ∧ (cell12641 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12641 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12641 ⟨23,by decide⟩).lower ∧ (cell12641 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12641 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12641 ⟨24,by decide⟩).lower ∧ (cell12641 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12641 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12641 ⟨25,by decide⟩).lower ∧ (cell12641 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12641 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12641 ⟨26,by decide⟩).lower ∧ (cell12641 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12641 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12641 ⟨27,by decide⟩).lower ∧ (cell12641 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12641 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12641 ⟨28,by decide⟩).lower ∧ (cell12641 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12641 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12641 ⟨29,by decide⟩).lower ∧ (cell12641 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12641 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12641 ⟨30,by decide⟩).lower ∧ (cell12641 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12641 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12641 ⟨31,by decide⟩).lower ∧ (cell12641 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12641 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12641 ⟨32,by decide⟩).lower ∧ (cell12641 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12641 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12641 ⟨33,by decide⟩).lower ∧ (cell12641 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12641 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12641 ⟨34,by decide⟩).lower ∧ (cell12641 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12641 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12641 ⟨35,by decide⟩).lower ∧ (cell12641 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12641 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12641 ⟨36,by decide⟩).lower ∧ (cell12641 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12641 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12641 ⟨37,by decide⟩).lower ∧ (cell12641 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12641 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12641 ⟨38,by decide⟩).lower ∧ (cell12641 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12641 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12641 ⟨39,by decide⟩).lower ∧ (cell12641 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12641 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12641 ⟨40,by decide⟩).lower ∧ (cell12641 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12641 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12641 ⟨41,by decide⟩).lower ∧ (cell12641 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12641 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12641 ⟨42,by decide⟩).lower ∧ (cell12641 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12641 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12641 ⟨43,by decide⟩).lower ∧ (cell12641 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12641 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12641 ⟨44,by decide⟩).lower ∧ (cell12641 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12641 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12641 ⟨45,by decide⟩).lower ∧ (cell12641 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12641 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12641 ⟨46,by decide⟩).lower ∧ (cell12641 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12641 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12641 ⟨47,by decide⟩).lower ∧ (cell12641 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12641 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12641 ⟨48,by decide⟩).lower ∧ (cell12641 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12641 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12641 ⟨49,by decide⟩).lower ∧ (cell12641 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12641 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12641 ⟨50,by decide⟩).lower ∧ (cell12641 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12641 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12641 ⟨51,by decide⟩).lower ∧ (cell12641 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12641 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12641 ⟨52,by decide⟩).lower ∧ (cell12641 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12641 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12641 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12641 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12641,cell12641,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12641 i).lower ∧
    (cell12641 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12641 i).upper ≤ (0.532 : ℝ) ∧
    (cell12641 i).centre ≤ (0.1 : ℝ) ∧ (cell12641 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12641 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12641 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12641

/-! The local source numeric instances at 12641 have no network premises. -/
namespace BstLean.Part269.N12641
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12641)
open BstLean.Part268 (cell12641)

noncomputable def sourceNumerics12641 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12641 (cell12641 i)
      scalarRow12641.M scalarRow12641.H scalarRow12641.xi := by
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
    energy_allowance := scalarRow12641.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12641]
    centre_nonneg := (scalarRow12641.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12641])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12641
/-! Actual 12642 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12642 ≤ (1.035891994568 : ℝ) := by
  have hr : (112.436648829463 : ℝ) ≤ √(12642 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.436648829463 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12642 12642 (11 / 1000) ≤
    (0.008501561154 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12642) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.436648829463 : ℝ) ≤ √(12642 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12642)
  have hdiv : K / √(12642 : ℝ) ≤ K / 112.436648829463 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.436648829463 ≤ (0.008501561154 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12642.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12642 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12642 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12642 := gPlus_lower 12642
end BstLean.Part269.N12642

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12642
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035891994567 : ℝ) ≤ wn 12642 := by
  have hn : √(12642 : ℝ) ≤ 112.436648829464 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12642 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.436648829464 ≤ 2 / √(12642 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253056689 : ℝ) ≤ rhoBar 12642 BstLean.Part154.csC ∧
    rhoBar 12642 BstLean.Part154.csC ≤ 0.000253057081 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035891994567 : ℝ) / (1.295212 * 12642) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035891994568 : ℝ) / (1.29521 * 12642) := by gcongr
      _ ≤ (0.000253057081 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12642 BstLean.Part154.csC) ≤ 0.001012292362 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12642 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) ≤ 0.000193286748 ∧
    cc1 (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) ≤ 0.000122989632 ∧
    cc2 (rhoBar 12642 BstLean.Part154.csC) ≤ 0.000071396413 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12642 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12642 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12642 BstLean.Part154.csC * nuR (rhoBar 12642 BstLean.Part154.csC)) ≤ 0.000506130172 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253057081 : ℝ) * 0.001012292362 := by gcongr
      _ ≤ (0.000506130172 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12642 BstLean.Part154.csC) * nuR (rhoBar 12642 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012292362 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12642 BstLean.Part154.csC) * rhoBar 12642 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253057081 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253057081 / 2 + 0.399 * 0.001012292362 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193286748 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506130172 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122989632 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253057081 / 1.414213562 := by gcongr
      _ ≤ (0.000071396413 : ℝ) := by norm_num

end BstLean.Part269.N12642

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12642
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) ≤ 1.61339E-7 := by
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12642 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12642 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12642 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193286748 : ℝ) ^ 2 + 0.000122989632 ^ 2 + 3 * 0.000071396413 ^ 2 +
        2 * 0.797885 * 0.000193286748 * 0.000122989632 + 2 * 0.000193286748 * 0.000071396413 +
        4 * 0.797885 * 0.000122989632 * 0.000071396413 := by gcongr
    _ ≤ (1.61339E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12642 BstLean.Part154.csC Θ ≤ 0.002641776105 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12642 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12642 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12642 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035891994568 * 1.61339E-7 / (0.000253056689 : ℝ) := by gcongr
    _ ≤ 0.002641776105 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12642 BstLean.Part154.csC Θ ≤ 0.002931425929 + 0.000667533670 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12642 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12642 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035891994568 : ℝ) * ((2 * Θ * 0.000253057081 +
        (6863 / 10000) * 0.000253057081 * 12642 * 0.001012292362) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002931425929 + 0.000667533670 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12642 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12642 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12642 0.011 Θ ∧ gammaRatio 12642 0.011 Θ ≤ 0.000086994481 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12642 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035891994568 : ℝ) * 0.525 / ((1 - 0.011) * 12642) := by gcongr
      _ ≤ (0.000086994481 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12642 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12642 0.011 Θ) :=
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
    badAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12642 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12642 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12642 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12642 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12642 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12642 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12642 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12642 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12642 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12642 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035891994568 : ℝ) * 12642 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003608132400 + 0.003309309775 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12642

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12642
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12642 BstLean.Part154.csC) (piBar (rhoBar 12642 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12642 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12642 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12642 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12642 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12642 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12642 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12642 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12642 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12642 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12642 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052605877933 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12642) ≤ 0.010621426319 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12642 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035891994568)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010621426319 + 2 * 0.737676 / 12642) := by gcongr
    _ ≤ (0.052605877933 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12642 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12642

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12642
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500933325 : ℝ) ≤ plow 12642 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12642) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852120032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386932456) : eMP 12642 0.011 xi bn ≤ 0.001193944751 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12642 : ℝ) * (1 - 0.011))) ≤ 0.000590332342 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386932456 / (12642 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590332342 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590332342 : ℝ) + 3.141593 * 0.052852120032 / (12642 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193944751 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852120032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386932456) : PiBarMP 12642 12 0.011 xi bn ≤ 0.161624433329 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12642 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037241542074 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.816537238460 : ℝ) ≤ √((12642 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.436648829463 : ℝ) ≤ √(12642 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12642) ≤ 0.123913407309 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037241542074 + 0.052852120032 * 1.772454 / (2 * (111.816537238460 : ℝ))) * (1 + 0.001193944751) +
        8 / (12642 * 112.436648829463) + 0.123913407309 := by gcongr
    _ ≤ (0.161624433329 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852120032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386932456) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282501767484) :
    parallelOracle 12642 0.011 xi bn cd ≤ 0.162619869312 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12642 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12642 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500933325 : ℝ) ≤ plow 12642 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.436648829463 : ℝ) ≤ √(12642 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282501767484 : ℝ) / (2 * 0.560500933325 * 112.436648829463)) * 0.161624433329 +
        0.282501767484 ^ 2 / (2 * 0.560500933325 * 112.436648829463) := by gcongr
    _ ≤ (0.162619869312 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052852120032) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386932456)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282501767484) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12642 12642 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500933325 : ℝ) ≤ plow 12642 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.436648829463 : ℝ) ≤ √(12642 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12642 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12642 Θ 1.22 ≤ 0.011794201569 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.436648829463 := by gcongr <;> linarith
      _ ≤ (0.011794201569 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12642 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12642 12642 0.011 ≤ 0.008501561154 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12642 12642 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12642 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12642 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12642 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12642 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162619869312 + 0.011794201569 + (0.008501561154 : ℝ) *
        (1 + 2 * (0.282501767484 + 0.011794201569) / (0.560500933325 * 112.436648829463))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12642]

end BstLean.Part269.N12642

/-! The original eight local profiles supply actual 12642 moment certificates. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12642 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052852120032 ∧
    0 ≤ bN 12642 BstLean.Part154.csC (groupTheta g) ∧ bN 12642 BstLean.Part154.csC (groupTheta g) ≤ 0.001386932456 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12642 12642 0.011
      (momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12642 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12642 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12642 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229895889551 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12642 0.011
      (momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12642 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12642
/-! The actual computed-centre upper energy formula at 12642. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12642

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12642)
open BstLean.Part268 (cell12642)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085661260871
  | 2 => 0.086607194438
  | 3 => 0.087551739004
  | 4 => 0.088496420721
  | 5 => 0.089443081900
  | 6 => 0.090393927489
  | 7 => 0.091351575844
  | 8 => 0.092319113811
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12642 12642 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12642 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12642

/-! Actual upper energy certificates on all 43 source endpoints at 12642. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12642)
open BstLean.Part268 (cell12642)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12642 (gMinus 12642) (1 - (cell12642 i).lower) ≤ 1 ∧
    energyUpper 12642 (gMinus 12642) (BstLean.Part211.gPlus 12642)
      (finiteEnergy 12642 12642 0.011) (1 - (cell12642 i).lower) ≤
      (cell12642 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨10,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨11,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨12,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨13,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨14,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨15,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨16,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨17,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨18,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨19,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨20,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨21,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨22,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨23,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨24,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨25,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨26,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨27,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨28,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨29,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨30,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨31,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨32,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨33,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨34,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨35,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨36,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨37,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨38,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨39,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨40,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨41,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨42,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨43,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨44,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨45,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨46,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨47,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨48,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨49,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨50,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨51,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12642) (by norm_num)
        (q := 1 - (cell12642 ⟨52,by decide⟩).lower)
        (by norm_num [cell12642]) (by norm_num [cell12642])
      exact ⟨E.1,E.2.trans (by norm_num [cell12642])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12642

/-! Source-cell containment and simple scalar guards at 12642. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12642)
open BstLean.Part268 (cell12642)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12642 ⟨10,by decide⟩).lower ∧ (cell12642 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12642 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12642 ⟨11,by decide⟩).lower ∧ (cell12642 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12642 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12642 ⟨12,by decide⟩).lower ∧ (cell12642 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12642 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12642 ⟨13,by decide⟩).lower ∧ (cell12642 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12642 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12642 ⟨14,by decide⟩).lower ∧ (cell12642 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12642 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12642 ⟨15,by decide⟩).lower ∧ (cell12642 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12642 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12642 ⟨16,by decide⟩).lower ∧ (cell12642 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12642 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12642 ⟨17,by decide⟩).lower ∧ (cell12642 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12642 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12642 ⟨18,by decide⟩).lower ∧ (cell12642 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12642 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12642 ⟨19,by decide⟩).lower ∧ (cell12642 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12642 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12642 ⟨20,by decide⟩).lower ∧ (cell12642 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12642 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12642 ⟨21,by decide⟩).lower ∧ (cell12642 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12642 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12642 ⟨22,by decide⟩).lower ∧ (cell12642 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12642 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12642 ⟨23,by decide⟩).lower ∧ (cell12642 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12642 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12642 ⟨24,by decide⟩).lower ∧ (cell12642 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12642 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12642 ⟨25,by decide⟩).lower ∧ (cell12642 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12642 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12642 ⟨26,by decide⟩).lower ∧ (cell12642 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12642 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12642 ⟨27,by decide⟩).lower ∧ (cell12642 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12642 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12642 ⟨28,by decide⟩).lower ∧ (cell12642 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12642 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12642 ⟨29,by decide⟩).lower ∧ (cell12642 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12642 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12642 ⟨30,by decide⟩).lower ∧ (cell12642 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12642 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12642 ⟨31,by decide⟩).lower ∧ (cell12642 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12642 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12642 ⟨32,by decide⟩).lower ∧ (cell12642 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12642 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12642 ⟨33,by decide⟩).lower ∧ (cell12642 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12642 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12642 ⟨34,by decide⟩).lower ∧ (cell12642 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12642 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12642 ⟨35,by decide⟩).lower ∧ (cell12642 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12642 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12642 ⟨36,by decide⟩).lower ∧ (cell12642 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12642 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12642 ⟨37,by decide⟩).lower ∧ (cell12642 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12642 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12642 ⟨38,by decide⟩).lower ∧ (cell12642 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12642 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12642 ⟨39,by decide⟩).lower ∧ (cell12642 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12642 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12642 ⟨40,by decide⟩).lower ∧ (cell12642 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12642 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12642 ⟨41,by decide⟩).lower ∧ (cell12642 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12642 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12642 ⟨42,by decide⟩).lower ∧ (cell12642 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12642 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12642 ⟨43,by decide⟩).lower ∧ (cell12642 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12642 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12642 ⟨44,by decide⟩).lower ∧ (cell12642 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12642 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12642 ⟨45,by decide⟩).lower ∧ (cell12642 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12642 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12642 ⟨46,by decide⟩).lower ∧ (cell12642 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12642 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12642 ⟨47,by decide⟩).lower ∧ (cell12642 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12642 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12642 ⟨48,by decide⟩).lower ∧ (cell12642 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12642 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12642 ⟨49,by decide⟩).lower ∧ (cell12642 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12642 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12642 ⟨50,by decide⟩).lower ∧ (cell12642 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12642 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12642 ⟨51,by decide⟩).lower ∧ (cell12642 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12642 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12642 ⟨52,by decide⟩).lower ∧ (cell12642 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12642 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12642 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12642 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12642,cell12642,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12642 i).lower ∧
    (cell12642 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12642 i).upper ≤ (0.532 : ℝ) ∧
    (cell12642 i).centre ≤ (0.1 : ℝ) ∧ (cell12642 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12642 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12642 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12642

/-! The local source numeric instances at 12642 have no network premises. -/
namespace BstLean.Part269.N12642
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12642)
open BstLean.Part268 (cell12642)

noncomputable def sourceNumerics12642 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12642 (cell12642 i)
      scalarRow12642.M scalarRow12642.H scalarRow12642.xi := by
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
    energy_allowance := scalarRow12642.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12642]
    centre_nonneg := (scalarRow12642.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12642])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12642
/-! Actual 12643 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12643 ≤ (1.035890562585 : ℝ) := by
  have hr : (112.441095690143 : ℝ) ≤ √(12643 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.441095690143 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12643 12643 (11 / 1000) ≤
    (0.008501224929 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12643) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.441095690143 : ℝ) ≤ √(12643 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12643)
  have hdiv : K / √(12643 : ℝ) ≤ K / 112.441095690143 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.441095690143 ≤ (0.008501224929 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12643.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12643 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12643 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12643 := gPlus_lower 12643
end BstLean.Part269.N12643

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12643
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035890562584 : ℝ) ≤ wn 12643 := by
  have hn : √(12643 : ℝ) ≤ 112.441095690144 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12643 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.441095690144 ≤ 2 / √(12643 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253036324 : ℝ) ≤ rhoBar 12643 BstLean.Part154.csC ∧
    rhoBar 12643 BstLean.Part154.csC ≤ 0.000253036716 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035890562584 : ℝ) / (1.295212 * 12643) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035890562585 : ℝ) / (1.29521 * 12643) := by gcongr
      _ ≤ (0.000253036716 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12643 BstLean.Part154.csC) ≤ 0.001012210892 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12643 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) ≤ 0.000193271192 ∧
    cc1 (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) ≤ 0.000122979734 ∧
    cc2 (rhoBar 12643 BstLean.Part154.csC) ≤ 0.000071390668 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12643 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12643 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12643 BstLean.Part154.csC * nuR (rhoBar 12643 BstLean.Part154.csC)) ≤ 0.000506089439 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253036716 : ℝ) * 0.001012210892 := by gcongr
      _ ≤ (0.000506089439 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12643 BstLean.Part154.csC) * nuR (rhoBar 12643 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012210892 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12643 BstLean.Part154.csC) * rhoBar 12643 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253036716 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253036716 / 2 + 0.399 * 0.001012210892 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193271192 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506089439 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122979734 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253036716 / 1.414213562 := by gcongr
      _ ≤ (0.000071390668 : ℝ) := by norm_num

end BstLean.Part269.N12643

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12643
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) ≤ 1.61313E-7 := by
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12643 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12643 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12643 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193271192 : ℝ) ^ 2 + 0.000122979734 ^ 2 + 3 * 0.000071390668 ^ 2 +
        2 * 0.797885 * 0.000193271192 * 0.000122979734 + 2 * 0.000193271192 * 0.000071390668 +
        4 * 0.797885 * 0.000122979734 * 0.000071390668 := by gcongr
    _ ≤ (1.61313E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12643 BstLean.Part154.csC Θ ≤ 0.002641559310 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12643 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12643 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12643 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035890562585 * 1.61313E-7 / (0.000253036324 : ℝ) := by gcongr
    _ ≤ 0.002641559310 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12643 BstLean.Part154.csC Θ ≤ 0.002931181906 + 0.000667479027 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12643 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12643 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035890562585 : ℝ) * ((2 * Θ * 0.000253036716 +
        (6863 / 10000) * 0.000253036716 * 12643 * 0.001012210892) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002931181906 + 0.000667479027 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12643 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12643 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12643 0.011 Θ ∧ gammaRatio 12643 0.011 Θ ≤ 0.000086987480 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12643 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035890562585 : ℝ) * 0.525 / ((1 - 0.011) * 12643) := by gcongr
      _ ≤ (0.000086987480 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12643 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12643 0.011 Θ) :=
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
    badAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12643 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12643 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12643 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12643 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12643 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12643 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12643 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12643 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12643 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12643 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035890562585 : ℝ) * 12643 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003607888377 + 0.003309038337 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12643

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12643
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12643 BstLean.Part154.csC) (piBar (rhoBar 12643 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12643 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12643 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12643 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12643 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12643 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12643 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12643 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12643 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12643 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12643 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052603774847 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12643) ≤ 0.010621006259 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12643 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035890562585)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010621006259 + 2 * 0.737676 / 12643) := by gcongr
    _ ≤ (0.052603774847 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12643 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12643

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12643
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500978960 : ℝ) ≤ plow 12643 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12643) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851733504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386818638) : eMP 12643 0.011 xi bn ≤ 0.001193848468 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12643 : ℝ) * (1 - 0.011))) ≤ 0.000590284774 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386818638 / (12643 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590284774 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590284774 : ℝ) + 3.141593 * 0.052851733504 / (12643 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193848468 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851733504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386818638) : PiBarMP 12643 12 0.011 xi bn ≤ 0.161617978848 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12643 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037240013937 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.820959573775 : ℝ) ≤ √((12643 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.441095690143 : ℝ) ≤ √(12643 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12643) ≤ 0.123908506737 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037240013937 + 0.052851733504 * 1.772454 / (2 * (111.820959573775 : ℝ))) * (1 + 0.001193848468) +
        8 / (12643 * 112.441095690143) + 0.123908506737 := by gcongr
    _ ≤ (0.161617978848 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851733504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386818638) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282498823737) :
    parallelOracle 12643 0.011 xi bn cd ≤ 0.162613343946 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12643 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12643 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500978960 : ℝ) ≤ plow 12643 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.441095690143 : ℝ) ≤ √(12643 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282498823737 : ℝ) / (2 * 0.560500978960 * 112.441095690143)) * 0.161617978848 +
        0.282498823737 ^ 2 / (2 * 0.560500978960 * 112.441095690143) := by gcongr
    _ ≤ (0.162613343946 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851733504) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386818638)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282498823737) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12643 12643 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500978960 : ℝ) ≤ plow 12643 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.441095690143 : ℝ) ≤ √(12643 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12643 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12643 Θ 1.22 ≤ 0.011793735128 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.441095690143 := by gcongr <;> linarith
      _ ≤ (0.011793735128 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12643 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12643 12643 0.011 ≤ 0.008501224929 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12643 12643 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12643 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12643 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12643 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12643 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162613343946 + 0.011793735128 + (0.008501224929 : ℝ) *
        (1 + 2 * (0.282498823737 + 0.011793735128) / (0.560500978960 * 112.441095690143))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12643]

end BstLean.Part269.N12643

/-! The original eight local profiles supply actual 12643 moment certificates. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12643 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052851733504 ∧
    0 ≤ bN 12643 BstLean.Part154.csC (groupTheta g) ∧ bN 12643 BstLean.Part154.csC (groupTheta g) ≤ 0.001386818638 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12643 12643 0.011
      (momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12643 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12643 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12643 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229895048890 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12643 0.011
      (momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12643 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12643
/-! The actual computed-centre upper energy formula at 12643. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12643

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12643)
open BstLean.Part268 (cell12643)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085658280389
  | 2 => 0.086604157721
  | 3 => 0.087548637612
  | 4 => 0.088493244288
  | 5 => 0.089439817793
  | 6 => 0.090390560435
  | 7 => 0.091348087505
  | 8 => 0.092315482315
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12643 12643 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12643 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12643

/-! Actual upper energy certificates on all 43 source endpoints at 12643. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12643)
open BstLean.Part268 (cell12643)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12643 (gMinus 12643) (1 - (cell12643 i).lower) ≤ 1 ∧
    energyUpper 12643 (gMinus 12643) (BstLean.Part211.gPlus 12643)
      (finiteEnergy 12643 12643 0.011) (1 - (cell12643 i).lower) ≤
      (cell12643 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨10,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨11,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨12,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨13,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨14,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨15,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨16,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨17,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨18,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨19,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨20,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨21,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨22,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨23,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨24,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨25,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨26,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨27,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨28,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨29,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨30,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨31,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨32,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨33,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨34,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨35,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨36,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨37,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨38,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨39,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨40,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨41,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨42,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨43,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨44,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨45,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨46,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨47,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨48,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨49,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨50,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨51,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12643) (by norm_num)
        (q := 1 - (cell12643 ⟨52,by decide⟩).lower)
        (by norm_num [cell12643]) (by norm_num [cell12643])
      exact ⟨E.1,E.2.trans (by norm_num [cell12643])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12643

/-! Source-cell containment and simple scalar guards at 12643. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12643)
open BstLean.Part268 (cell12643)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12643 ⟨10,by decide⟩).lower ∧ (cell12643 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12643 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12643 ⟨11,by decide⟩).lower ∧ (cell12643 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12643 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12643 ⟨12,by decide⟩).lower ∧ (cell12643 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12643 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12643 ⟨13,by decide⟩).lower ∧ (cell12643 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12643 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12643 ⟨14,by decide⟩).lower ∧ (cell12643 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12643 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12643 ⟨15,by decide⟩).lower ∧ (cell12643 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12643 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12643 ⟨16,by decide⟩).lower ∧ (cell12643 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12643 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12643 ⟨17,by decide⟩).lower ∧ (cell12643 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12643 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12643 ⟨18,by decide⟩).lower ∧ (cell12643 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12643 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12643 ⟨19,by decide⟩).lower ∧ (cell12643 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12643 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12643 ⟨20,by decide⟩).lower ∧ (cell12643 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12643 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12643 ⟨21,by decide⟩).lower ∧ (cell12643 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12643 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12643 ⟨22,by decide⟩).lower ∧ (cell12643 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12643 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12643 ⟨23,by decide⟩).lower ∧ (cell12643 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12643 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12643 ⟨24,by decide⟩).lower ∧ (cell12643 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12643 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12643 ⟨25,by decide⟩).lower ∧ (cell12643 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12643 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12643 ⟨26,by decide⟩).lower ∧ (cell12643 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12643 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12643 ⟨27,by decide⟩).lower ∧ (cell12643 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12643 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12643 ⟨28,by decide⟩).lower ∧ (cell12643 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12643 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12643 ⟨29,by decide⟩).lower ∧ (cell12643 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12643 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12643 ⟨30,by decide⟩).lower ∧ (cell12643 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12643 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12643 ⟨31,by decide⟩).lower ∧ (cell12643 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12643 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12643 ⟨32,by decide⟩).lower ∧ (cell12643 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12643 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12643 ⟨33,by decide⟩).lower ∧ (cell12643 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12643 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12643 ⟨34,by decide⟩).lower ∧ (cell12643 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12643 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12643 ⟨35,by decide⟩).lower ∧ (cell12643 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12643 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12643 ⟨36,by decide⟩).lower ∧ (cell12643 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12643 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12643 ⟨37,by decide⟩).lower ∧ (cell12643 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12643 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12643 ⟨38,by decide⟩).lower ∧ (cell12643 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12643 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12643 ⟨39,by decide⟩).lower ∧ (cell12643 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12643 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12643 ⟨40,by decide⟩).lower ∧ (cell12643 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12643 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12643 ⟨41,by decide⟩).lower ∧ (cell12643 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12643 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12643 ⟨42,by decide⟩).lower ∧ (cell12643 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12643 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12643 ⟨43,by decide⟩).lower ∧ (cell12643 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12643 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12643 ⟨44,by decide⟩).lower ∧ (cell12643 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12643 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12643 ⟨45,by decide⟩).lower ∧ (cell12643 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12643 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12643 ⟨46,by decide⟩).lower ∧ (cell12643 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12643 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12643 ⟨47,by decide⟩).lower ∧ (cell12643 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12643 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12643 ⟨48,by decide⟩).lower ∧ (cell12643 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12643 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12643 ⟨49,by decide⟩).lower ∧ (cell12643 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12643 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12643 ⟨50,by decide⟩).lower ∧ (cell12643 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12643 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12643 ⟨51,by decide⟩).lower ∧ (cell12643 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12643 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12643 ⟨52,by decide⟩).lower ∧ (cell12643 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12643 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12643 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12643 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12643,cell12643,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12643 i).lower ∧
    (cell12643 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12643 i).upper ≤ (0.532 : ℝ) ∧
    (cell12643 i).centre ≤ (0.1 : ℝ) ∧ (cell12643 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12643 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12643 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12643

/-! The local source numeric instances at 12643 have no network premises. -/
namespace BstLean.Part269.N12643
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12643)
open BstLean.Part268 (cell12643)

noncomputable def sourceNumerics12643 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12643 (cell12643 i)
      scalarRow12643.M scalarRow12643.H scalarRow12643.xi := by
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
    energy_allowance := scalarRow12643.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12643]
    centre_nonneg := (scalarRow12643.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12643])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12643
/-! Actual 12644 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12644 ≤ (1.035889130774 : ℝ) := by
  have hr : (112.445542374964 : ℝ) ≤ √(12644 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.445542374964 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12644 12644 (11 / 1000) ≤
    (0.008500888743 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12644) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.445542374964 : ℝ) ≤ √(12644 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12644)
  have hdiv : K / √(12644 : ℝ) ≤ K / 112.445542374964 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.445542374964 ≤ (0.008500888743 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12644.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12644 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12644 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12644 := gPlus_lower 12644
end BstLean.Part269.N12644

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12644
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035889130773 : ℝ) ≤ wn 12644 := by
  have hn : √(12644 : ℝ) ≤ 112.445542374965 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12644 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.445542374965 ≤ 2 / √(12644 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253015962 : ℝ) ≤ rhoBar 12644 BstLean.Part154.csC ∧
    rhoBar 12644 BstLean.Part154.csC ≤ 0.000253016354 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035889130773 : ℝ) / (1.295212 * 12644) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035889130774 : ℝ) / (1.29521 * 12644) := by gcongr
      _ ≤ (0.000253016354 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12644 BstLean.Part154.csC) ≤ 0.001012129434 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12644 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) ≤ 0.000193255639 ∧
    cc1 (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) ≤ 0.000122969838 ∧
    cc2 (rhoBar 12644 BstLean.Part154.csC) ≤ 0.000071384923 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12644 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12644 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12644 BstLean.Part154.csC * nuR (rhoBar 12644 BstLean.Part154.csC)) ≤ 0.000506048713 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253016354 : ℝ) * 0.001012129434 := by gcongr
      _ ≤ (0.000506048713 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12644 BstLean.Part154.csC) * nuR (rhoBar 12644 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012129434 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12644 BstLean.Part154.csC) * rhoBar 12644 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253016354 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253016354 / 2 + 0.399 * 0.001012129434 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193255639 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506048713 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122969838 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253016354 / 1.414213562 := by gcongr
      _ ≤ (0.000071384923 : ℝ) := by norm_num

end BstLean.Part269.N12644

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12644
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) ≤ 1.61287E-7 := by
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12644 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12644 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12644 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193255639 : ℝ) ^ 2 + 0.000122969838 ^ 2 + 3 * 0.000071384923 ^ 2 +
        2 * 0.797885 * 0.000193255639 * 0.000122969838 + 2 * 0.000193255639 * 0.000071384923 +
        4 * 0.797885 * 0.000122969838 * 0.000071384923 := by gcongr
    _ ≤ (1.61287E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12644 BstLean.Part154.csC Θ ≤ 0.002641342450 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12644 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12644 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12644 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035889130774 * 1.61287E-7 / (0.000253015962 : ℝ) := by gcongr
    _ ≤ 0.002641342450 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12644 BstLean.Part154.csC Θ ≤ 0.002930937917 + 0.000667424392 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12644 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12644 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035889130774 : ℝ) * ((2 * Θ * 0.000253016354 +
        (6863 / 10000) * 0.000253016354 * 12644 * 0.001012129434) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002930937917 + 0.000667424392 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12644 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12644 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12644 0.011 Θ ∧ gammaRatio 12644 0.011 Θ ≤ 0.000086980480 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12644 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035889130774 : ℝ) * 0.525 / ((1 - 0.011) * 12644) := by gcongr
      _ ≤ (0.000086980480 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12644 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12644 0.011 Θ) :=
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
    badAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12644 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12644 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12644 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12644 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12644 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12644 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12644 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12644 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12644 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12644 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035889130774 : ℝ) * 12644 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003607644388 + 0.003308766842 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12644

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12644
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12644 BstLean.Part154.csC) (piBar (rhoBar 12644 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12644 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12644 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12644 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12644 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12644 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12644 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12644 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12644 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12644 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12644 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052601672013 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12644) ≤ 0.010620586249 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12644 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035889130774)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010620586249 + 2 * 0.737676 / 12644) := by gcongr
    _ ≤ (0.052601672013 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12644 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12644

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12644
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501024588 : ℝ) ≤ plow 12644 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12644) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851346981)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386704787) : eMP 12644 0.011 xi bn ≤ 0.001193752174 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12644 : ℝ) * (1 - 0.011))) ≤ 0.000590237201 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386704787 / (12644 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590237201 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590237201 : ℝ) + 3.141593 * 0.052851346981 / (12644 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193752174 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851346981)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386704787) : PiBarMP 12644 12 0.011 xi bn ≤ 0.161611524446 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12644 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037238485295 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.825381734202 : ℝ) ≤ √((12644 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.445542374964 : ℝ) ≤ √(12644 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12644) ≤ 0.123903606746 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037238485295 + 0.052851346981 * 1.772454 / (2 * (111.825381734202 : ℝ))) * (1 + 0.001193752174) +
        8 / (12644 * 112.445542374964) + 0.123903606746 := by gcongr
    _ ≤ (0.161611524446 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851346981)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386704787) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282495880251) :
    parallelOracle 12644 0.011 xi bn cd ≤ 0.162606818669 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12644 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12644 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501024588 : ℝ) ≤ plow 12644 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.445542374964 : ℝ) ≤ √(12644 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282495880251 : ℝ) / (2 * 0.560501024588 * 112.445542374964)) * 0.161611524446 +
        0.282495880251 ^ 2 / (2 * 0.560501024588 * 112.445542374964) := by gcongr
    _ ≤ (0.162606818669 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052851346981) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386704787)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282495880251) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12644 12644 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501024588 : ℝ) ≤ plow 12644 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.445542374964 : ℝ) ≤ √(12644 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12644 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12644 Θ 1.22 ≤ 0.011793268742 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.445542374964 := by gcongr <;> linarith
      _ ≤ (0.011793268742 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12644 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12644 12644 0.011 ≤ 0.008500888743 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12644 12644 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12644 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12644 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12644 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12644 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162606818669 + 0.011793268742 + (0.008500888743 : ℝ) *
        (1 + 2 * (0.282495880251 + 0.011793268742) / (0.560501024588 * 112.445542374964))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12644]

end BstLean.Part269.N12644

/-! The original eight local profiles supply actual 12644 moment certificates. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12644 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052851346981 ∧
    0 ≤ bN 12644 BstLean.Part154.csC (groupTheta g) ∧ bN 12644 BstLean.Part154.csC (groupTheta g) ≤ 0.001386704787 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12644 12644 0.011
      (momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12644 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12644 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12644 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229894208238 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12644 0.011
      (momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12644 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12644
/-! The actual computed-centre upper energy formula at 12644. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12644

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12644)
open BstLean.Part268 (cell12644)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085655301055
  | 2 => 0.086601122201
  | 3 => 0.087545537476
  | 4 => 0.088490069183
  | 5 => 0.089436555104
  | 6 => 0.090387194907
  | 7 => 0.091344600822
  | 8 => 0.092311852632
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12644 12644 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12644 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12644

/-! Actual upper energy certificates on all 43 source endpoints at 12644. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12644)
open BstLean.Part268 (cell12644)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12644 (gMinus 12644) (1 - (cell12644 i).lower) ≤ 1 ∧
    energyUpper 12644 (gMinus 12644) (BstLean.Part211.gPlus 12644)
      (finiteEnergy 12644 12644 0.011) (1 - (cell12644 i).lower) ≤
      (cell12644 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨10,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨11,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨12,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨13,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨14,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨15,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨16,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨17,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨18,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨19,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨20,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨21,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨22,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨23,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨24,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨25,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨26,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨27,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨28,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨29,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨30,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨31,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨32,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨33,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨34,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨35,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨36,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨37,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨38,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨39,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨40,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨41,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨42,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨43,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨44,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨45,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨46,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨47,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨48,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨49,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨50,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨51,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12644) (by norm_num)
        (q := 1 - (cell12644 ⟨52,by decide⟩).lower)
        (by norm_num [cell12644]) (by norm_num [cell12644])
      exact ⟨E.1,E.2.trans (by norm_num [cell12644])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12644

/-! Source-cell containment and simple scalar guards at 12644. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12644)
open BstLean.Part268 (cell12644)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12644 ⟨10,by decide⟩).lower ∧ (cell12644 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12644 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12644 ⟨11,by decide⟩).lower ∧ (cell12644 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12644 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12644 ⟨12,by decide⟩).lower ∧ (cell12644 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12644 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12644 ⟨13,by decide⟩).lower ∧ (cell12644 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12644 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12644 ⟨14,by decide⟩).lower ∧ (cell12644 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12644 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12644 ⟨15,by decide⟩).lower ∧ (cell12644 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12644 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12644 ⟨16,by decide⟩).lower ∧ (cell12644 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12644 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12644 ⟨17,by decide⟩).lower ∧ (cell12644 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12644 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12644 ⟨18,by decide⟩).lower ∧ (cell12644 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12644 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12644 ⟨19,by decide⟩).lower ∧ (cell12644 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12644 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12644 ⟨20,by decide⟩).lower ∧ (cell12644 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12644 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12644 ⟨21,by decide⟩).lower ∧ (cell12644 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12644 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12644 ⟨22,by decide⟩).lower ∧ (cell12644 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12644 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12644 ⟨23,by decide⟩).lower ∧ (cell12644 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12644 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12644 ⟨24,by decide⟩).lower ∧ (cell12644 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12644 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12644 ⟨25,by decide⟩).lower ∧ (cell12644 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12644 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12644 ⟨26,by decide⟩).lower ∧ (cell12644 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12644 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12644 ⟨27,by decide⟩).lower ∧ (cell12644 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12644 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12644 ⟨28,by decide⟩).lower ∧ (cell12644 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12644 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12644 ⟨29,by decide⟩).lower ∧ (cell12644 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12644 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12644 ⟨30,by decide⟩).lower ∧ (cell12644 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12644 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12644 ⟨31,by decide⟩).lower ∧ (cell12644 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12644 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12644 ⟨32,by decide⟩).lower ∧ (cell12644 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12644 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12644 ⟨33,by decide⟩).lower ∧ (cell12644 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12644 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12644 ⟨34,by decide⟩).lower ∧ (cell12644 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12644 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12644 ⟨35,by decide⟩).lower ∧ (cell12644 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12644 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12644 ⟨36,by decide⟩).lower ∧ (cell12644 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12644 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12644 ⟨37,by decide⟩).lower ∧ (cell12644 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12644 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12644 ⟨38,by decide⟩).lower ∧ (cell12644 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12644 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12644 ⟨39,by decide⟩).lower ∧ (cell12644 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12644 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12644 ⟨40,by decide⟩).lower ∧ (cell12644 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12644 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12644 ⟨41,by decide⟩).lower ∧ (cell12644 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12644 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12644 ⟨42,by decide⟩).lower ∧ (cell12644 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12644 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12644 ⟨43,by decide⟩).lower ∧ (cell12644 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12644 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12644 ⟨44,by decide⟩).lower ∧ (cell12644 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12644 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12644 ⟨45,by decide⟩).lower ∧ (cell12644 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12644 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12644 ⟨46,by decide⟩).lower ∧ (cell12644 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12644 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12644 ⟨47,by decide⟩).lower ∧ (cell12644 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12644 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12644 ⟨48,by decide⟩).lower ∧ (cell12644 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12644 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12644 ⟨49,by decide⟩).lower ∧ (cell12644 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12644 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12644 ⟨50,by decide⟩).lower ∧ (cell12644 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12644 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12644 ⟨51,by decide⟩).lower ∧ (cell12644 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12644 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12644 ⟨52,by decide⟩).lower ∧ (cell12644 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12644 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12644 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12644 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12644,cell12644,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12644 i).lower ∧
    (cell12644 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12644 i).upper ≤ (0.532 : ℝ) ∧
    (cell12644 i).centre ≤ (0.1 : ℝ) ∧ (cell12644 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12644 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12644 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12644

/-! The local source numeric instances at 12644 have no network premises. -/
namespace BstLean.Part269.N12644
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12644)
open BstLean.Part268 (cell12644)

noncomputable def sourceNumerics12644 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12644 (cell12644 i)
      scalarRow12644.M scalarRow12644.H scalarRow12644.xi := by
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
    energy_allowance := scalarRow12644.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12644]
    centre_nonneg := (scalarRow12644.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12644])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12644
/-! Actual 12645 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12645 ≤ (1.035887699133 : ℝ) := by
  have hr : (112.449988883947 : ℝ) ≤ √(12645 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.449988883947 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12645 12645 (11 / 1000) ≤
    (0.008500552598 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12645) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.449988883947 : ℝ) ≤ √(12645 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12645)
  have hdiv : K / √(12645 : ℝ) ≤ K / 112.449988883947 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.449988883947 ≤ (0.008500552598 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12645.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12645 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12645 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12645 := gPlus_lower 12645
end BstLean.Part269.N12645

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12645
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035887699132 : ℝ) ≤ wn 12645 := by
  have hn : √(12645 : ℝ) ≤ 112.449988883948 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12645 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.449988883948 ≤ 2 / √(12645 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252995603 : ℝ) ≤ rhoBar 12645 BstLean.Part154.csC ∧
    rhoBar 12645 BstLean.Part154.csC ≤ 0.000252995995 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035887699132 : ℝ) / (1.295212 * 12645) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035887699133 : ℝ) / (1.29521 * 12645) := by gcongr
      _ ≤ (0.000252995995 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12645 BstLean.Part154.csC) ≤ 0.001012047987 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12645 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) ≤ 0.000193240087 ∧
    cc1 (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) ≤ 0.000122959943 ∧
    cc2 (rhoBar 12645 BstLean.Part154.csC) ≤ 0.000071379179 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12645 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12645 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12645 BstLean.Part154.csC * nuR (rhoBar 12645 BstLean.Part154.csC)) ≤ 0.000506007992 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252995995 : ℝ) * 0.001012047987 := by gcongr
      _ ≤ (0.000506007992 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12645 BstLean.Part154.csC) * nuR (rhoBar 12645 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012047987 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12645 BstLean.Part154.csC) * rhoBar 12645 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252995995 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252995995 / 2 + 0.399 * 0.001012047987 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193240087 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506007992 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122959943 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252995995 / 1.414213562 := by gcongr
      _ ≤ (0.000071379179 : ℝ) := by norm_num

end BstLean.Part269.N12645

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12645
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) ≤ 1.61261E-7 := by
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12645 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12645 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12645 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193240087 : ℝ) ^ 2 + 0.000122959943 ^ 2 + 3 * 0.000071379179 ^ 2 +
        2 * 0.797885 * 0.000193240087 * 0.000122959943 + 2 * 0.000193240087 * 0.000071379179 +
        4 * 0.797885 * 0.000122959943 * 0.000071379179 := by gcongr
    _ ≤ (1.61261E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12645 BstLean.Part154.csC Θ ≤ 0.002641125526 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12645 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12645 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12645 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035887699133 * 1.61261E-7 / (0.000252995603 : ℝ) := by gcongr
    _ ≤ 0.002641125526 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12645 BstLean.Part154.csC Θ ≤ 0.002930693960 + 0.000667369765 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12645 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12645 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035887699133 : ℝ) * ((2 * Θ * 0.000252995995 +
        (6863 / 10000) * 0.000252995995 * 12645 * 0.001012047987) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002930693960 + 0.000667369765 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12645 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12645 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12645 0.011 Θ ∧ gammaRatio 12645 0.011 Θ ≤ 0.000086973481 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12645 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035887699133 : ℝ) * 0.525 / ((1 - 0.011) * 12645) := by gcongr
      _ ≤ (0.000086973481 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12645 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12645 0.011 Θ) :=
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
    badAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12645 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12645 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12645 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12645 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12645 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12645 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12645 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12645 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12645 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12645 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035887699133 : ℝ) * 12645 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003607400431 + 0.003308495291 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12645

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12645
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12645 BstLean.Part154.csC) (piBar (rhoBar 12645 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12645 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12645 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12645 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12645 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12645 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12645 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12645 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12645 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12645 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12645 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052599569431 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12645) ≤ 0.010620166289 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12645 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035887699133)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010620166289 + 2 * 0.737676 / 12645) := by gcongr
    _ ≤ (0.052599569431 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12645 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12645

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12645
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501070209 : ℝ) ≤ plow 12645 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12645) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850960459)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386590902) : eMP 12645 0.011 xi bn ≤ 0.001193655877 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12645 : ℝ) * (1 - 0.011))) ≤ 0.000590189626 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386590902 / (12645 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590189626 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590189626 : ℝ) + 3.141593 * 0.052850960459 / (12645 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193655877 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850960459)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386590902) : PiBarMP 12645 12 0.011 xi bn ≤ 0.161605070107 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12645 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037236956133 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.829803719759 : ℝ) ≤ √((12645 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.449988883947 : ℝ) ≤ √(12645 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12645) ≤ 0.123898707337 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037236956133 + 0.052850960459 * 1.772454 / (2 * (111.829803719759 : ℝ))) * (1 + 0.001193655877) +
        8 / (12645 * 112.449988883947) + 0.123898707337 := by gcongr
    _ ≤ (0.161605070107 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850960459)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386590902) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282492937015) :
    parallelOracle 12645 0.011 xi bn cd ≤ 0.162600293464 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12645 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12645 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501070209 : ℝ) ≤ plow 12645 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.449988883947 : ℝ) ≤ √(12645 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282492937015 : ℝ) / (2 * 0.560501070209 * 112.449988883947)) * 0.161605070107 +
        0.282492937015 ^ 2 / (2 * 0.560501070209 * 112.449988883947) := by gcongr
    _ ≤ (0.162600293464 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850960459) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386590902)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282492937015) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12645 12645 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501070209 : ℝ) ≤ plow 12645 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.449988883947 : ℝ) ≤ √(12645 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12645 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12645 Θ 1.22 ≤ 0.011792802411 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.449988883947 := by gcongr <;> linarith
      _ ≤ (0.011792802411 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12645 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12645 12645 0.011 ≤ 0.008500552598 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12645 12645 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12645 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12645 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12645 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12645 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162600293464 + 0.011792802411 + (0.008500552598 : ℝ) *
        (1 + 2 * (0.282492937015 + 0.011792802411) / (0.560501070209 * 112.449988883947))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12645]

end BstLean.Part269.N12645

/-! The original eight local profiles supply actual 12645 moment certificates. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12645 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052850960459 ∧
    0 ≤ bN 12645 BstLean.Part154.csC (groupTheta g) ∧ bN 12645 BstLean.Part154.csC (groupTheta g) ≤ 0.001386590902 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12645 12645 0.011
      (momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12645 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12645 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12645 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229893367584 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12645 0.011
      (momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12645 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12645
/-! The actual computed-centre upper energy formula at 12645. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12645

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12645)
open BstLean.Part268 (cell12645)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085652322870
  | 2 => 0.086598087877
  | 3 => 0.087542438595
  | 4 => 0.088486895405
  | 5 => 0.089433293831
  | 6 => 0.090383830903
  | 7 => 0.091341115793
  | 8 => 0.092308224760
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12645 12645 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12645 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12645

/-! Actual upper energy certificates on all 43 source endpoints at 12645. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12645)
open BstLean.Part268 (cell12645)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12645 (gMinus 12645) (1 - (cell12645 i).lower) ≤ 1 ∧
    energyUpper 12645 (gMinus 12645) (BstLean.Part211.gPlus 12645)
      (finiteEnergy 12645 12645 0.011) (1 - (cell12645 i).lower) ≤
      (cell12645 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨10,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨11,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨12,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨13,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨14,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨15,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨16,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨17,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨18,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨19,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨20,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨21,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨22,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨23,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨24,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨25,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨26,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨27,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨28,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨29,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨30,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨31,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨32,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨33,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨34,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨35,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨36,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨37,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨38,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨39,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨40,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨41,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨42,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨43,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨44,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨45,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨46,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨47,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨48,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨49,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨50,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨51,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12645) (by norm_num)
        (q := 1 - (cell12645 ⟨52,by decide⟩).lower)
        (by norm_num [cell12645]) (by norm_num [cell12645])
      exact ⟨E.1,E.2.trans (by norm_num [cell12645])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12645

/-! Source-cell containment and simple scalar guards at 12645. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12645)
open BstLean.Part268 (cell12645)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12645 ⟨10,by decide⟩).lower ∧ (cell12645 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12645 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12645 ⟨11,by decide⟩).lower ∧ (cell12645 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12645 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12645 ⟨12,by decide⟩).lower ∧ (cell12645 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12645 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12645 ⟨13,by decide⟩).lower ∧ (cell12645 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12645 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12645 ⟨14,by decide⟩).lower ∧ (cell12645 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12645 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12645 ⟨15,by decide⟩).lower ∧ (cell12645 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12645 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12645 ⟨16,by decide⟩).lower ∧ (cell12645 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12645 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12645 ⟨17,by decide⟩).lower ∧ (cell12645 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12645 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12645 ⟨18,by decide⟩).lower ∧ (cell12645 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12645 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12645 ⟨19,by decide⟩).lower ∧ (cell12645 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12645 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12645 ⟨20,by decide⟩).lower ∧ (cell12645 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12645 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12645 ⟨21,by decide⟩).lower ∧ (cell12645 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12645 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12645 ⟨22,by decide⟩).lower ∧ (cell12645 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12645 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12645 ⟨23,by decide⟩).lower ∧ (cell12645 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12645 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12645 ⟨24,by decide⟩).lower ∧ (cell12645 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12645 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12645 ⟨25,by decide⟩).lower ∧ (cell12645 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12645 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12645 ⟨26,by decide⟩).lower ∧ (cell12645 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12645 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12645 ⟨27,by decide⟩).lower ∧ (cell12645 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12645 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12645 ⟨28,by decide⟩).lower ∧ (cell12645 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12645 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12645 ⟨29,by decide⟩).lower ∧ (cell12645 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12645 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12645 ⟨30,by decide⟩).lower ∧ (cell12645 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12645 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12645 ⟨31,by decide⟩).lower ∧ (cell12645 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12645 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12645 ⟨32,by decide⟩).lower ∧ (cell12645 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12645 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12645 ⟨33,by decide⟩).lower ∧ (cell12645 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12645 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12645 ⟨34,by decide⟩).lower ∧ (cell12645 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12645 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12645 ⟨35,by decide⟩).lower ∧ (cell12645 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12645 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12645 ⟨36,by decide⟩).lower ∧ (cell12645 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12645 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12645 ⟨37,by decide⟩).lower ∧ (cell12645 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12645 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12645 ⟨38,by decide⟩).lower ∧ (cell12645 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12645 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12645 ⟨39,by decide⟩).lower ∧ (cell12645 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12645 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12645 ⟨40,by decide⟩).lower ∧ (cell12645 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12645 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12645 ⟨41,by decide⟩).lower ∧ (cell12645 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12645 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12645 ⟨42,by decide⟩).lower ∧ (cell12645 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12645 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12645 ⟨43,by decide⟩).lower ∧ (cell12645 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12645 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12645 ⟨44,by decide⟩).lower ∧ (cell12645 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12645 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12645 ⟨45,by decide⟩).lower ∧ (cell12645 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12645 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12645 ⟨46,by decide⟩).lower ∧ (cell12645 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12645 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12645 ⟨47,by decide⟩).lower ∧ (cell12645 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12645 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12645 ⟨48,by decide⟩).lower ∧ (cell12645 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12645 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12645 ⟨49,by decide⟩).lower ∧ (cell12645 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12645 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12645 ⟨50,by decide⟩).lower ∧ (cell12645 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12645 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12645 ⟨51,by decide⟩).lower ∧ (cell12645 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12645 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12645 ⟨52,by decide⟩).lower ∧ (cell12645 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12645 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12645 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12645 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12645,cell12645,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12645 i).lower ∧
    (cell12645 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12645 i).upper ≤ (0.532 : ℝ) ∧
    (cell12645 i).centre ≤ (0.1 : ℝ) ∧ (cell12645 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12645 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12645 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12645

/-! The local source numeric instances at 12645 have no network premises. -/
namespace BstLean.Part269.N12645
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12645)
open BstLean.Part268 (cell12645)

noncomputable def sourceNumerics12645 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12645 (cell12645 i)
      scalarRow12645.M scalarRow12645.H scalarRow12645.xi := by
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
    energy_allowance := scalarRow12645.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12645]
    centre_nonneg := (scalarRow12645.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12645])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12645
/-! Actual 12646 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12646 ≤ (1.035886267664 : ℝ) := by
  have hr : (112.454435217113 : ℝ) ≤ √(12646 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.454435217113 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12646 12646 (11 / 1000) ≤
    (0.008500216492 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12646) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.454435217113 : ℝ) ≤ √(12646 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12646)
  have hdiv : K / √(12646 : ℝ) ≤ K / 112.454435217113 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.454435217113 ≤ (0.008500216492 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12646.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12646 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12646 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12646 := gPlus_lower 12646
end BstLean.Part269.N12646

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12646
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035886267663 : ℝ) ≤ wn 12646 := by
  have hn : √(12646 : ℝ) ≤ 112.454435217114 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12646 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.454435217114 ≤ 2 / √(12646 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252975247 : ℝ) ≤ rhoBar 12646 BstLean.Part154.csC ∧
    rhoBar 12646 BstLean.Part154.csC ≤ 0.000252975639 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035886267663 : ℝ) / (1.295212 * 12646) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035886267664 : ℝ) / (1.29521 * 12646) := by gcongr
      _ ≤ (0.000252975639 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12646 BstLean.Part154.csC) ≤ 0.001011966553 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12646 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) ≤ 0.000193224539 ∧
    cc1 (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) ≤ 0.000122950049 ∧
    cc2 (rhoBar 12646 BstLean.Part154.csC) ≤ 0.000071373436 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12646 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12646 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12646 BstLean.Part154.csC * nuR (rhoBar 12646 BstLean.Part154.csC)) ≤ 0.000505967277 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252975639 : ℝ) * 0.001011966553 := by gcongr
      _ ≤ (0.000505967277 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12646 BstLean.Part154.csC) * nuR (rhoBar 12646 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011966553 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12646 BstLean.Part154.csC) * rhoBar 12646 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252975639 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252975639 / 2 + 0.399 * 0.001011966553 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193224539 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505967277 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122950049 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252975639 / 1.414213562 := by gcongr
      _ ≤ (0.000071373436 : ℝ) := by norm_num

end BstLean.Part269.N12646

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12646
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) ≤ 1.61235E-7 := by
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12646 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12646 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12646 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193224539 : ℝ) ^ 2 + 0.000122950049 ^ 2 + 3 * 0.000071373436 ^ 2 +
        2 * 0.797885 * 0.000193224539 * 0.000122950049 + 2 * 0.000193224539 * 0.000071373436 +
        4 * 0.797885 * 0.000122950049 * 0.000071373436 := by gcongr
    _ ≤ (1.61235E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12646 BstLean.Part154.csC Θ ≤ 0.002640908538 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12646 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12646 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12646 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035886267664 * 1.61235E-7 / (0.000252975247 : ℝ) := by gcongr
    _ ≤ 0.002640908538 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12646 BstLean.Part154.csC Θ ≤ 0.002930450039 + 0.000667315146 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12646 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12646 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035886267664 : ℝ) * ((2 * Θ * 0.000252975639 +
        (6863 / 10000) * 0.000252975639 * 12646 * 0.001011966553) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002930450039 + 0.000667315146 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12646 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12646 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12646 0.011 Θ ∧ gammaRatio 12646 0.011 Θ ≤ 0.000086966483 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12646 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035886267664 : ℝ) * 0.525 / ((1 - 0.011) * 12646) := by gcongr
      _ ≤ (0.000086966483 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12646 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12646 0.011 Θ) :=
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
    badAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12646 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12646 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12646 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12646 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12646 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12646 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12646 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12646 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12646 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12646 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035886267664 : ℝ) * 12646 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003607156510 + 0.003308223684 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12646

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12646
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12646 BstLean.Part154.csC) (piBar (rhoBar 12646 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12646 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12646 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12646 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12646 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12646 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12646 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12646 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12646 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12646 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12646 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052597467096 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12646) ≤ 0.010619746378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12646 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035886267664)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010619746378 + 2 * 0.737676 / 12646) := by gcongr
    _ ≤ (0.052597467096 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12646 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12646

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12646
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501115823 : ℝ) ≤ plow 12646 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12646) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850573945)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386476983) : eMP 12646 0.011 xi bn ≤ 0.001193559570 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12646 : ℝ) * (1 - 0.011))) ≤ 0.000590142046 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386476983 / (12646 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590142046 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590142046 : ℝ) + 3.141593 * 0.052850573945 / (12646 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193559570 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850573945)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386476983) : PiBarMP 12646 12 0.011 xi bn ≤ 0.161598615832 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12646 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037235426452 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.834225530469 : ℝ) ≤ √((12646 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.454435217113 : ℝ) ≤ √(12646 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12646) ≤ 0.123893808509 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037235426452 + 0.052850573945 * 1.772454 / (2 * (111.834225530469 : ℝ))) * (1 + 0.001193559570) +
        8 / (12646 * 112.454435217113) + 0.123893808509 := by gcongr
    _ ≤ (0.161598615832 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850573945)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386476983) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282489994041) :
    parallelOracle 12646 0.011 xi bn cd ≤ 0.162593768332 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12646 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12646 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501115823 : ℝ) ≤ plow 12646 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.454435217113 : ℝ) ≤ √(12646 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282489994041 : ℝ) / (2 * 0.560501115823 * 112.454435217113)) * 0.161598615832 +
        0.282489994041 ^ 2 / (2 * 0.560501115823 * 112.454435217113) := by gcongr
    _ ≤ (0.162593768332 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850573945) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386476983)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282489994041) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12646 12646 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501115823 : ℝ) ≤ plow 12646 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.454435217113 : ℝ) ≤ √(12646 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12646 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12646 Θ 1.22 ≤ 0.011792336136 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.454435217113 := by gcongr <;> linarith
      _ ≤ (0.011792336136 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12646 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12646 12646 0.011 ≤ 0.008500216492 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12646 12646 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12646 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12646 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12646 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12646 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162593768332 + 0.011792336136 + (0.008500216492 : ℝ) *
        (1 + 2 * (0.282489994041 + 0.011792336136) / (0.560501115823 * 112.454435217113))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12646]

end BstLean.Part269.N12646

/-! The original eight local profiles supply actual 12646 moment certificates. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12646 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052850573945 ∧
    0 ≤ bN 12646 BstLean.Part154.csC (groupTheta g) ∧ bN 12646 BstLean.Part154.csC (groupTheta g) ≤ 0.001386476983 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12646 12646 0.011
      (momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12646 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12646 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12646 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229892526945 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12646 0.011
      (momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12646 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12646
/-! The actual computed-centre upper energy formula at 12646. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12646

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12646)
open BstLean.Part268 (cell12646)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085649345831
  | 2 => 0.086595054746
  | 3 => 0.087539340968
  | 4 => 0.088483722954
  | 5 => 0.089430033972
  | 6 => 0.090380468420
  | 7 => 0.091337632416
  | 8 => 0.092304598697
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12646 12646 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12646 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12646

/-! Actual upper energy certificates on all 43 source endpoints at 12646. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12646)
open BstLean.Part268 (cell12646)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12646 (gMinus 12646) (1 - (cell12646 i).lower) ≤ 1 ∧
    energyUpper 12646 (gMinus 12646) (BstLean.Part211.gPlus 12646)
      (finiteEnergy 12646 12646 0.011) (1 - (cell12646 i).lower) ≤
      (cell12646 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨10,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨11,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨12,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨13,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨14,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨15,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨16,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨17,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨18,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨19,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨20,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨21,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨22,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨23,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨24,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨25,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨26,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨27,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨28,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨29,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨30,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨31,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨32,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨33,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨34,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨35,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨36,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨37,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨38,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨39,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨40,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨41,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨42,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨43,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨44,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨45,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨46,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨47,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨48,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨49,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨50,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨51,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12646) (by norm_num)
        (q := 1 - (cell12646 ⟨52,by decide⟩).lower)
        (by norm_num [cell12646]) (by norm_num [cell12646])
      exact ⟨E.1,E.2.trans (by norm_num [cell12646])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12646

/-! Source-cell containment and simple scalar guards at 12646. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12646)
open BstLean.Part268 (cell12646)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12646 ⟨10,by decide⟩).lower ∧ (cell12646 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12646 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12646 ⟨11,by decide⟩).lower ∧ (cell12646 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12646 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12646 ⟨12,by decide⟩).lower ∧ (cell12646 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12646 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12646 ⟨13,by decide⟩).lower ∧ (cell12646 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12646 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12646 ⟨14,by decide⟩).lower ∧ (cell12646 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12646 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12646 ⟨15,by decide⟩).lower ∧ (cell12646 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12646 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12646 ⟨16,by decide⟩).lower ∧ (cell12646 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12646 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12646 ⟨17,by decide⟩).lower ∧ (cell12646 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12646 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12646 ⟨18,by decide⟩).lower ∧ (cell12646 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12646 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12646 ⟨19,by decide⟩).lower ∧ (cell12646 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12646 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12646 ⟨20,by decide⟩).lower ∧ (cell12646 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12646 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12646 ⟨21,by decide⟩).lower ∧ (cell12646 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12646 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12646 ⟨22,by decide⟩).lower ∧ (cell12646 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12646 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12646 ⟨23,by decide⟩).lower ∧ (cell12646 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12646 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12646 ⟨24,by decide⟩).lower ∧ (cell12646 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12646 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12646 ⟨25,by decide⟩).lower ∧ (cell12646 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12646 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12646 ⟨26,by decide⟩).lower ∧ (cell12646 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12646 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12646 ⟨27,by decide⟩).lower ∧ (cell12646 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12646 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12646 ⟨28,by decide⟩).lower ∧ (cell12646 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12646 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12646 ⟨29,by decide⟩).lower ∧ (cell12646 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12646 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12646 ⟨30,by decide⟩).lower ∧ (cell12646 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12646 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12646 ⟨31,by decide⟩).lower ∧ (cell12646 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12646 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12646 ⟨32,by decide⟩).lower ∧ (cell12646 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12646 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12646 ⟨33,by decide⟩).lower ∧ (cell12646 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12646 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12646 ⟨34,by decide⟩).lower ∧ (cell12646 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12646 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12646 ⟨35,by decide⟩).lower ∧ (cell12646 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12646 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12646 ⟨36,by decide⟩).lower ∧ (cell12646 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12646 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12646 ⟨37,by decide⟩).lower ∧ (cell12646 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12646 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12646 ⟨38,by decide⟩).lower ∧ (cell12646 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12646 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12646 ⟨39,by decide⟩).lower ∧ (cell12646 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12646 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12646 ⟨40,by decide⟩).lower ∧ (cell12646 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12646 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12646 ⟨41,by decide⟩).lower ∧ (cell12646 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12646 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12646 ⟨42,by decide⟩).lower ∧ (cell12646 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12646 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12646 ⟨43,by decide⟩).lower ∧ (cell12646 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12646 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12646 ⟨44,by decide⟩).lower ∧ (cell12646 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12646 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12646 ⟨45,by decide⟩).lower ∧ (cell12646 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12646 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12646 ⟨46,by decide⟩).lower ∧ (cell12646 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12646 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12646 ⟨47,by decide⟩).lower ∧ (cell12646 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12646 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12646 ⟨48,by decide⟩).lower ∧ (cell12646 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12646 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12646 ⟨49,by decide⟩).lower ∧ (cell12646 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12646 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12646 ⟨50,by decide⟩).lower ∧ (cell12646 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12646 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12646 ⟨51,by decide⟩).lower ∧ (cell12646 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12646 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12646 ⟨52,by decide⟩).lower ∧ (cell12646 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12646 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12646 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12646 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12646,cell12646,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12646 i).lower ∧
    (cell12646 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12646 i).upper ≤ (0.532 : ℝ) ∧
    (cell12646 i).centre ≤ (0.1 : ℝ) ∧ (cell12646 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12646 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12646 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12646

/-! The local source numeric instances at 12646 have no network premises. -/
namespace BstLean.Part269.N12646
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12646)
open BstLean.Part268 (cell12646)

noncomputable def sourceNumerics12646 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12646 (cell12646 i)
      scalarRow12646.M scalarRow12646.H scalarRow12646.xi := by
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
    energy_allowance := scalarRow12646.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12646]
    centre_nonneg := (scalarRow12646.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12646])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12646
/-! Actual 12647 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12647 ≤ (1.035884836365 : ℝ) := by
  have hr : (112.458881374482 : ℝ) ≤ √(12647 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.458881374482 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12647 12647 (11 / 1000) ≤
    (0.008499880426 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12647) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.458881374482 : ℝ) ≤ √(12647 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12647)
  have hdiv : K / √(12647 : ℝ) ≤ K / 112.458881374482 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.458881374482 ≤ (0.008499880426 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12647.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12647 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12647 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12647 := gPlus_lower 12647
end BstLean.Part269.N12647

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12647
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035884836364 : ℝ) ≤ wn 12647 := by
  have hn : √(12647 : ℝ) ≤ 112.458881374483 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12647 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.458881374483 ≤ 2 / √(12647 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252954895 : ℝ) ≤ rhoBar 12647 BstLean.Part154.csC ∧
    rhoBar 12647 BstLean.Part154.csC ≤ 0.000252955287 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035884836364 : ℝ) / (1.295212 * 12647) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035884836365 : ℝ) / (1.29521 * 12647) := by gcongr
      _ ≤ (0.000252955287 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12647 BstLean.Part154.csC) ≤ 0.001011885135 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12647 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) ≤ 0.000193208993 ∧
    cc1 (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) ≤ 0.000122940157 ∧
    cc2 (rhoBar 12647 BstLean.Part154.csC) ≤ 0.000071367694 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12647 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12647 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12647 BstLean.Part154.csC * nuR (rhoBar 12647 BstLean.Part154.csC)) ≤ 0.000505926571 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252955287 : ℝ) * 0.001011885135 := by gcongr
      _ ≤ (0.000505926571 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12647 BstLean.Part154.csC) * nuR (rhoBar 12647 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011885135 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12647 BstLean.Part154.csC) * rhoBar 12647 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252955287 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252955287 / 2 + 0.399 * 0.001011885135 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193208993 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505926571 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122940157 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252955287 / 1.414213562 := by gcongr
      _ ≤ (0.000071367694 : ℝ) := by norm_num

end BstLean.Part269.N12647

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12647
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) ≤ 1.61209E-7 := by
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12647 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12647 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12647 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193208993 : ℝ) ^ 2 + 0.000122940157 ^ 2 + 3 * 0.000071367694 ^ 2 +
        2 * 0.797885 * 0.000193208993 * 0.000122940157 + 2 * 0.000193208993 * 0.000071367694 +
        4 * 0.797885 * 0.000122940157 * 0.000071367694 := by gcongr
    _ ≤ (1.61209E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12647 BstLean.Part154.csC Θ ≤ 0.002640691474 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12647 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12647 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12647 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035884836365 * 1.61209E-7 / (0.000252954895 : ℝ) := by gcongr
    _ ≤ 0.002640691474 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12647 BstLean.Part154.csC Θ ≤ 0.002930206175 + 0.000667260539 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12647 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12647 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035884836365 : ℝ) * ((2 * Θ * 0.000252955287 +
        (6863 / 10000) * 0.000252955287 * 12647 * 0.001011885135) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002930206175 + 0.000667260539 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12647 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12647 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12647 0.011 Θ ∧ gammaRatio 12647 0.011 Θ ≤ 0.000086959487 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12647 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035884836365 : ℝ) * 0.525 / ((1 - 0.011) * 12647) := by gcongr
      _ ≤ (0.000086959487 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12647 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12647 0.011 Θ) :=
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
    badAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12647 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12647 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12647 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12647 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12647 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12647 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12647 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12647 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12647 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12647 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035884836365 : ℝ) * 12647 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003606912646 + 0.003307952013 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12647

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12647
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12647 BstLean.Part154.csC) (piBar (rhoBar 12647 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12647 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12647 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12647 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12647 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12647 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12647 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12647 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12647 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12647 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12647 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052595365019 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12647) ≤ 0.010619326518 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12647 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035884836365)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010619326518 + 2 * 0.737676 / 12647) := by gcongr
    _ ≤ (0.052595365019 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12647 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12647

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12647
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501161429 : ℝ) ≤ plow 12647 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12647) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850187453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386363024) : eMP 12647 0.011 xi bn ≤ 0.001193463255 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12647 : ℝ) * (1 - 0.011))) ≤ 0.000590094462 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386363024 / (12647 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590094462 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590094462 : ℝ) + 3.141593 * 0.052850187453 / (12647 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193463255 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850187453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386363024) : PiBarMP 12647 12 0.011 xi bn ≤ 0.161592161539 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12647 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037233896171 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.838647166353 : ℝ) ≤ √((12647 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.458881374482 : ℝ) ≤ √(12647 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12647) ≤ 0.123888910262 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037233896171 + 0.052850187453 * 1.772454 / (2 * (111.838647166353 : ℝ))) * (1 + 0.001193463255) +
        8 / (12647 * 112.458881374482) + 0.123888910262 := by gcongr
    _ ≤ (0.161592161539 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850187453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386363024) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282487051370) :
    parallelOracle 12647 0.011 xi bn cd ≤ 0.162587243191 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12647 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12647 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501161429 : ℝ) ≤ plow 12647 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.458881374482 : ℝ) ≤ √(12647 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282487051370 : ℝ) / (2 * 0.560501161429 * 112.458881374482)) * 0.161592161539 +
        0.282487051370 ^ 2 / (2 * 0.560501161429 * 112.458881374482) := by gcongr
    _ ≤ (0.162587243191 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052850187453) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386363024)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282487051370) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12647 12647 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501161429 : ℝ) ≤ plow 12647 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.458881374482 : ℝ) ≤ √(12647 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12647 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12647 Θ 1.22 ≤ 0.011791869916 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.458881374482 := by gcongr <;> linarith
      _ ≤ (0.011791869916 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12647 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12647 12647 0.011 ≤ 0.008499880426 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12647 12647 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12647 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12647 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12647 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12647 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162587243191 + 0.011791869916 + (0.008499880426 : ℝ) *
        (1 + 2 * (0.282487051370 + 0.011791869916) / (0.560501161429 * 112.458881374482))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12647]

end BstLean.Part269.N12647

/-! The original eight local profiles supply actual 12647 moment certificates. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12647 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052850187453 ∧
    0 ≤ bN 12647 BstLean.Part154.csC (groupTheta g) ∧ bN 12647 BstLean.Part154.csC (groupTheta g) ≤ 0.001386363024 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12647 12647 0.011
      (momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12647 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12647 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12647 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229891686351 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12647 0.011
      (momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12647 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12647
/-! The actual computed-centre upper energy formula at 12647. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12647

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12647)
open BstLean.Part268 (cell12647)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085646369937
  | 2 => 0.086592022809
  | 3 => 0.087536244592
  | 4 => 0.088480551826
  | 5 => 0.089426775526
  | 6 => 0.090377107458
  | 7 => 0.091334150690
  | 8 => 0.092300974440
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12647 12647 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12647 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12647

/-! Actual upper energy certificates on all 43 source endpoints at 12647. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12647)
open BstLean.Part268 (cell12647)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12647 (gMinus 12647) (1 - (cell12647 i).lower) ≤ 1 ∧
    energyUpper 12647 (gMinus 12647) (BstLean.Part211.gPlus 12647)
      (finiteEnergy 12647 12647 0.011) (1 - (cell12647 i).lower) ≤
      (cell12647 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨10,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨11,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨12,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨13,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨14,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨15,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨16,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨17,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨18,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨19,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨20,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨21,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨22,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨23,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨24,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨25,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨26,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨27,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨28,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨29,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨30,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨31,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨32,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨33,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨34,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨35,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨36,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨37,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨38,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨39,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨40,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨41,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨42,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨43,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨44,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨45,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨46,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨47,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨48,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨49,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨50,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨51,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12647) (by norm_num)
        (q := 1 - (cell12647 ⟨52,by decide⟩).lower)
        (by norm_num [cell12647]) (by norm_num [cell12647])
      exact ⟨E.1,E.2.trans (by norm_num [cell12647])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12647

/-! Source-cell containment and simple scalar guards at 12647. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12647)
open BstLean.Part268 (cell12647)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12647 ⟨10,by decide⟩).lower ∧ (cell12647 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12647 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12647 ⟨11,by decide⟩).lower ∧ (cell12647 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12647 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12647 ⟨12,by decide⟩).lower ∧ (cell12647 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12647 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12647 ⟨13,by decide⟩).lower ∧ (cell12647 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12647 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12647 ⟨14,by decide⟩).lower ∧ (cell12647 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12647 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12647 ⟨15,by decide⟩).lower ∧ (cell12647 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12647 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12647 ⟨16,by decide⟩).lower ∧ (cell12647 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12647 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12647 ⟨17,by decide⟩).lower ∧ (cell12647 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12647 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12647 ⟨18,by decide⟩).lower ∧ (cell12647 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12647 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12647 ⟨19,by decide⟩).lower ∧ (cell12647 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12647 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12647 ⟨20,by decide⟩).lower ∧ (cell12647 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12647 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12647 ⟨21,by decide⟩).lower ∧ (cell12647 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12647 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12647 ⟨22,by decide⟩).lower ∧ (cell12647 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12647 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12647 ⟨23,by decide⟩).lower ∧ (cell12647 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12647 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12647 ⟨24,by decide⟩).lower ∧ (cell12647 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12647 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12647 ⟨25,by decide⟩).lower ∧ (cell12647 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12647 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12647 ⟨26,by decide⟩).lower ∧ (cell12647 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12647 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12647 ⟨27,by decide⟩).lower ∧ (cell12647 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12647 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12647 ⟨28,by decide⟩).lower ∧ (cell12647 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12647 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12647 ⟨29,by decide⟩).lower ∧ (cell12647 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12647 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12647 ⟨30,by decide⟩).lower ∧ (cell12647 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12647 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12647 ⟨31,by decide⟩).lower ∧ (cell12647 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12647 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12647 ⟨32,by decide⟩).lower ∧ (cell12647 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12647 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12647 ⟨33,by decide⟩).lower ∧ (cell12647 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12647 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12647 ⟨34,by decide⟩).lower ∧ (cell12647 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12647 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12647 ⟨35,by decide⟩).lower ∧ (cell12647 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12647 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12647 ⟨36,by decide⟩).lower ∧ (cell12647 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12647 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12647 ⟨37,by decide⟩).lower ∧ (cell12647 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12647 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12647 ⟨38,by decide⟩).lower ∧ (cell12647 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12647 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12647 ⟨39,by decide⟩).lower ∧ (cell12647 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12647 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12647 ⟨40,by decide⟩).lower ∧ (cell12647 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12647 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12647 ⟨41,by decide⟩).lower ∧ (cell12647 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12647 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12647 ⟨42,by decide⟩).lower ∧ (cell12647 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12647 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12647 ⟨43,by decide⟩).lower ∧ (cell12647 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12647 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12647 ⟨44,by decide⟩).lower ∧ (cell12647 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12647 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12647 ⟨45,by decide⟩).lower ∧ (cell12647 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12647 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12647 ⟨46,by decide⟩).lower ∧ (cell12647 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12647 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12647 ⟨47,by decide⟩).lower ∧ (cell12647 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12647 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12647 ⟨48,by decide⟩).lower ∧ (cell12647 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12647 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12647 ⟨49,by decide⟩).lower ∧ (cell12647 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12647 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12647 ⟨50,by decide⟩).lower ∧ (cell12647 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12647 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12647 ⟨51,by decide⟩).lower ∧ (cell12647 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12647 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12647 ⟨52,by decide⟩).lower ∧ (cell12647 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12647 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12647 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12647 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12647,cell12647,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12647 i).lower ∧
    (cell12647 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12647 i).upper ≤ (0.532 : ℝ) ∧
    (cell12647 i).centre ≤ (0.1 : ℝ) ∧ (cell12647 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12647 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12647 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12647

/-! The local source numeric instances at 12647 have no network premises. -/
namespace BstLean.Part269.N12647
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12647)
open BstLean.Part268 (cell12647)

noncomputable def sourceNumerics12647 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12647 (cell12647 i)
      scalarRow12647.M scalarRow12647.H scalarRow12647.xi := by
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
    energy_allowance := scalarRow12647.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12647]
    centre_nonneg := (scalarRow12647.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12647])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12647
/-! Actual 12648 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12648 ≤ (1.035883405236 : ℝ) := by
  have hr : (112.463327356076 : ℝ) ≤ √(12648 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.463327356076 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12648 12648 (11 / 1000) ≤
    (0.008499544400 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12648) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.463327356076 : ℝ) ≤ √(12648 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12648)
  have hdiv : K / √(12648 : ℝ) ≤ K / 112.463327356076 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.463327356076 ≤ (0.008499544400 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12648.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12648 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12648 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12648 := gPlus_lower 12648
end BstLean.Part269.N12648

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12648
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035883405235 : ℝ) ≤ wn 12648 := by
  have hn : √(12648 : ℝ) ≤ 112.463327356077 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12648 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.463327356077 ≤ 2 / √(12648 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252934546 : ℝ) ≤ rhoBar 12648 BstLean.Part154.csC ∧
    rhoBar 12648 BstLean.Part154.csC ≤ 0.000252934938 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035883405235 : ℝ) / (1.295212 * 12648) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035883405236 : ℝ) / (1.29521 * 12648) := by gcongr
      _ ≤ (0.000252934938 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12648 BstLean.Part154.csC) ≤ 0.001011803729 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12648 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) ≤ 0.000193193450 ∧
    cc1 (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) ≤ 0.000122930267 ∧
    cc2 (rhoBar 12648 BstLean.Part154.csC) ≤ 0.000071361952 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12648 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12648 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12648 BstLean.Part154.csC * nuR (rhoBar 12648 BstLean.Part154.csC)) ≤ 0.000505885870 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252934938 : ℝ) * 0.001011803729 := by gcongr
      _ ≤ (0.000505885870 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12648 BstLean.Part154.csC) * nuR (rhoBar 12648 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011803729 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12648 BstLean.Part154.csC) * rhoBar 12648 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252934938 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252934938 / 2 + 0.399 * 0.001011803729 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193193450 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505885870 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122930267 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252934938 / 1.414213562 := by gcongr
      _ ≤ (0.000071361952 : ℝ) := by norm_num

end BstLean.Part269.N12648

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12648
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) ≤ 1.61183E-7 := by
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12648 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12648 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12648 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193193450 : ℝ) ^ 2 + 0.000122930267 ^ 2 + 3 * 0.000071361952 ^ 2 +
        2 * 0.797885 * 0.000193193450 * 0.000122930267 + 2 * 0.000193193450 * 0.000071361952 +
        4 * 0.797885 * 0.000122930267 * 0.000071361952 := by gcongr
    _ ≤ (1.61183E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12648 BstLean.Part154.csC Θ ≤ 0.002640474345 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12648 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12648 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12648 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035883405236 * 1.61183E-7 / (0.000252934546 : ℝ) := by gcongr
    _ ≤ 0.002640474345 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12648 BstLean.Part154.csC Θ ≤ 0.002929962346 + 0.000667205939 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12648 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12648 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035883405236 : ℝ) * ((2 * Θ * 0.000252934938 +
        (6863 / 10000) * 0.000252934938 * 12648 * 0.001011803729) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002929962346 + 0.000667205939 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12648 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12648 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12648 0.011 Θ ∧ gammaRatio 12648 0.011 Θ ≤ 0.000086952491 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12648 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035883405236 : ℝ) * 0.525 / ((1 - 0.011) * 12648) := by gcongr
      _ ≤ (0.000086952491 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12648 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12648 0.011 Θ) :=
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
    badAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12648 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12648 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12648 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12648 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12648 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12648 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12648 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12648 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12648 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12648 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035883405236 : ℝ) * 12648 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003606668817 + 0.003307680284 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12648

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12648
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12648 BstLean.Part154.csC) (piBar (rhoBar 12648 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12648 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12648 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12648 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12648 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12648 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12648 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12648 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12648 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12648 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12648 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052593263188 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12648) ≤ 0.010618906707 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12648 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035883405236)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010618906707 + 2 * 0.737676 / 12648) := by gcongr
    _ ≤ (0.052593263188 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12648 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12648

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12648
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501207028 : ℝ) ≤ plow 12648 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12648) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849800967)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386249032) : eMP 12648 0.011 xi bn ≤ 0.001193366935 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12648 : ℝ) * (1 - 0.011))) ≤ 0.000590046875 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386249032 / (12648 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590046875 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590046875 : ℝ) + 3.141593 * 0.052849800967 / (12648 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193366935 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849800967)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386249032) : PiBarMP 12648 12 0.011 xi bn ≤ 0.161585707323 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12648 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037232365383 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.843068627429 : ℝ) ≤ √((12648 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.463327356076 : ℝ) ≤ √(12648 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12648) ≤ 0.123884012596 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037232365383 + 0.052849800967 * 1.772454 / (2 * (111.843068627429 : ℝ))) * (1 + 0.001193366935) +
        8 / (12648 * 112.463327356076) + 0.123884012596 := by gcongr
    _ ≤ (0.161585707323 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849800967)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386249032) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282484108954) :
    parallelOracle 12648 0.011 xi bn cd ≤ 0.162580718136 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12648 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12648 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501207028 : ℝ) ≤ plow 12648 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.463327356076 : ℝ) ≤ √(12648 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282484108954 : ℝ) / (2 * 0.560501207028 * 112.463327356076)) * 0.161585707323 +
        0.282484108954 ^ 2 / (2 * 0.560501207028 * 112.463327356076) := by gcongr
    _ ≤ (0.162580718136 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849800967) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386249032)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282484108954) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12648 12648 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501207028 : ℝ) ≤ plow 12648 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.463327356076 : ℝ) ≤ √(12648 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12648 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12648 Θ 1.22 ≤ 0.011791403751 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.463327356076 := by gcongr <;> linarith
      _ ≤ (0.011791403751 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12648 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12648 12648 0.011 ≤ 0.008499544400 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12648 12648 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12648 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12648 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12648 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12648 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162580718136 + 0.011791403751 + (0.008499544400 : ℝ) *
        (1 + 2 * (0.282484108954 + 0.011791403751) / (0.560501207028 * 112.463327356076))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12648]

end BstLean.Part269.N12648

/-! The original eight local profiles supply actual 12648 moment certificates. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12648 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052849800967 ∧
    0 ≤ bN 12648 BstLean.Part154.csC (groupTheta g) ∧ bN 12648 BstLean.Part154.csC (groupTheta g) ≤ 0.001386249032 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12648 12648 0.011
      (momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12648 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12648 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12648 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229890845766 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12648 0.011
      (momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12648 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12648
/-! The actual computed-centre upper energy formula at 12648. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12648

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12648)
open BstLean.Part268 (cell12648)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085643395188
  | 2 => 0.086588992064
  | 3 => 0.087533149467
  | 4 => 0.088477382022
  | 5 => 0.089423518492
  | 6 => 0.090373748015
  | 7 => 0.091330670612
  | 8 => 0.092297351987
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12648 12648 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12648 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12648

/-! Actual upper energy certificates on all 43 source endpoints at 12648. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12648)
open BstLean.Part268 (cell12648)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12648 (gMinus 12648) (1 - (cell12648 i).lower) ≤ 1 ∧
    energyUpper 12648 (gMinus 12648) (BstLean.Part211.gPlus 12648)
      (finiteEnergy 12648 12648 0.011) (1 - (cell12648 i).lower) ≤
      (cell12648 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨10,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨11,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨12,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨13,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨14,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨15,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨16,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨17,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨18,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨19,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨20,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨21,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨22,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨23,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨24,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨25,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨26,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨27,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨28,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨29,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨30,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨31,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨32,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨33,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨34,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨35,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨36,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨37,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨38,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨39,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨40,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨41,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨42,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨43,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨44,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨45,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨46,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨47,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨48,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨49,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨50,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨51,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12648) (by norm_num)
        (q := 1 - (cell12648 ⟨52,by decide⟩).lower)
        (by norm_num [cell12648]) (by norm_num [cell12648])
      exact ⟨E.1,E.2.trans (by norm_num [cell12648])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12648

/-! Source-cell containment and simple scalar guards at 12648. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12648)
open BstLean.Part268 (cell12648)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12648 ⟨10,by decide⟩).lower ∧ (cell12648 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12648 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12648 ⟨11,by decide⟩).lower ∧ (cell12648 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12648 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12648 ⟨12,by decide⟩).lower ∧ (cell12648 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12648 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12648 ⟨13,by decide⟩).lower ∧ (cell12648 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12648 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12648 ⟨14,by decide⟩).lower ∧ (cell12648 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12648 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12648 ⟨15,by decide⟩).lower ∧ (cell12648 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12648 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12648 ⟨16,by decide⟩).lower ∧ (cell12648 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12648 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12648 ⟨17,by decide⟩).lower ∧ (cell12648 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12648 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12648 ⟨18,by decide⟩).lower ∧ (cell12648 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12648 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12648 ⟨19,by decide⟩).lower ∧ (cell12648 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12648 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12648 ⟨20,by decide⟩).lower ∧ (cell12648 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12648 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12648 ⟨21,by decide⟩).lower ∧ (cell12648 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12648 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12648 ⟨22,by decide⟩).lower ∧ (cell12648 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12648 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12648 ⟨23,by decide⟩).lower ∧ (cell12648 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12648 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12648 ⟨24,by decide⟩).lower ∧ (cell12648 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12648 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12648 ⟨25,by decide⟩).lower ∧ (cell12648 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12648 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12648 ⟨26,by decide⟩).lower ∧ (cell12648 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12648 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12648 ⟨27,by decide⟩).lower ∧ (cell12648 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12648 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12648 ⟨28,by decide⟩).lower ∧ (cell12648 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12648 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12648 ⟨29,by decide⟩).lower ∧ (cell12648 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12648 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12648 ⟨30,by decide⟩).lower ∧ (cell12648 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12648 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12648 ⟨31,by decide⟩).lower ∧ (cell12648 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12648 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12648 ⟨32,by decide⟩).lower ∧ (cell12648 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12648 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12648 ⟨33,by decide⟩).lower ∧ (cell12648 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12648 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12648 ⟨34,by decide⟩).lower ∧ (cell12648 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12648 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12648 ⟨35,by decide⟩).lower ∧ (cell12648 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12648 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12648 ⟨36,by decide⟩).lower ∧ (cell12648 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12648 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12648 ⟨37,by decide⟩).lower ∧ (cell12648 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12648 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12648 ⟨38,by decide⟩).lower ∧ (cell12648 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12648 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12648 ⟨39,by decide⟩).lower ∧ (cell12648 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12648 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12648 ⟨40,by decide⟩).lower ∧ (cell12648 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12648 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12648 ⟨41,by decide⟩).lower ∧ (cell12648 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12648 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12648 ⟨42,by decide⟩).lower ∧ (cell12648 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12648 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12648 ⟨43,by decide⟩).lower ∧ (cell12648 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12648 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12648 ⟨44,by decide⟩).lower ∧ (cell12648 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12648 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12648 ⟨45,by decide⟩).lower ∧ (cell12648 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12648 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12648 ⟨46,by decide⟩).lower ∧ (cell12648 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12648 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12648 ⟨47,by decide⟩).lower ∧ (cell12648 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12648 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12648 ⟨48,by decide⟩).lower ∧ (cell12648 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12648 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12648 ⟨49,by decide⟩).lower ∧ (cell12648 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12648 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12648 ⟨50,by decide⟩).lower ∧ (cell12648 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12648 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12648 ⟨51,by decide⟩).lower ∧ (cell12648 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12648 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12648 ⟨52,by decide⟩).lower ∧ (cell12648 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12648 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12648 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12648 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12648,cell12648,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12648 i).lower ∧
    (cell12648 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12648 i).upper ≤ (0.532 : ℝ) ∧
    (cell12648 i).centre ≤ (0.1 : ℝ) ∧ (cell12648 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12648 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12648 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12648

/-! The local source numeric instances at 12648 have no network premises. -/
namespace BstLean.Part269.N12648
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12648)
open BstLean.Part268 (cell12648)

noncomputable def sourceNumerics12648 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12648 (cell12648 i)
      scalarRow12648.M scalarRow12648.H scalarRow12648.xi := by
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
    energy_allowance := scalarRow12648.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12648]
    centre_nonneg := (scalarRow12648.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12648])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12648
/-! Actual 12649 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12649 ≤ (1.035881974279 : ℝ) := by
  have hr : (112.467773161915 : ℝ) ≤ √(12649 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.467773161915 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12649 12649 (11 / 1000) ≤
    (0.008499208414 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12649) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.467773161915 : ℝ) ≤ √(12649 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12649)
  have hdiv : K / √(12649 : ℝ) ≤ K / 112.467773161915 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.467773161915 ≤ (0.008499208414 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12649.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12649 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12649 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12649 := gPlus_lower 12649
end BstLean.Part269.N12649

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12649
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035881974278 : ℝ) ≤ wn 12649 := by
  have hn : √(12649 : ℝ) ≤ 112.467773161916 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12649 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.467773161916 ≤ 2 / √(12649 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252914200 : ℝ) ≤ rhoBar 12649 BstLean.Part154.csC ∧
    rhoBar 12649 BstLean.Part154.csC ≤ 0.000252914592 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035881974278 : ℝ) / (1.295212 * 12649) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035881974279 : ℝ) / (1.29521 * 12649) := by gcongr
      _ ≤ (0.000252914592 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12649 BstLean.Part154.csC) ≤ 0.001011722334 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12649 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) ≤ 0.000193177908 ∧
    cc1 (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) ≤ 0.000122920378 ∧
    cc2 (rhoBar 12649 BstLean.Part154.csC) ≤ 0.000071356212 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12649 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12649 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12649 BstLean.Part154.csC * nuR (rhoBar 12649 BstLean.Part154.csC)) ≤ 0.000505845176 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252914592 : ℝ) * 0.001011722334 := by gcongr
      _ ≤ (0.000505845176 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12649 BstLean.Part154.csC) * nuR (rhoBar 12649 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011722334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12649 BstLean.Part154.csC) * rhoBar 12649 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252914592 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252914592 / 2 + 0.399 * 0.001011722334 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193177908 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505845176 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122920378 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252914592 / 1.414213562 := by gcongr
      _ ≤ (0.000071356212 : ℝ) := by norm_num

end BstLean.Part269.N12649

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12649
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) ≤ 1.61157E-7 := by
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12649 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12649 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12649 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193177908 : ℝ) ^ 2 + 0.000122920378 ^ 2 + 3 * 0.000071356212 ^ 2 +
        2 * 0.797885 * 0.000193177908 * 0.000122920378 + 2 * 0.000193177908 * 0.000071356212 +
        4 * 0.797885 * 0.000122920378 * 0.000071356212 := by gcongr
    _ ≤ (1.61157E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12649 BstLean.Part154.csC Θ ≤ 0.002640257152 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12649 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12649 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12649 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035881974279 * 1.61157E-7 / (0.000252914200 : ℝ) := by gcongr
    _ ≤ 0.002640257152 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12649 BstLean.Part154.csC Θ ≤ 0.002929718547 + 0.000667151348 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12649 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12649 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035881974279 : ℝ) * ((2 * Θ * 0.000252914592 +
        (6863 / 10000) * 0.000252914592 * 12649 * 0.001011722334) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002929718547 + 0.000667151348 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12649 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12649 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12649 0.011 Θ ∧ gammaRatio 12649 0.011 Θ ≤ 0.000086945497 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12649 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035881974279 : ℝ) * 0.525 / ((1 - 0.011) * 12649) := by gcongr
      _ ≤ (0.000086945497 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12649 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12649 0.011 Θ) :=
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
    badAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12649 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12649 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12649 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12649 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12649 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12649 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12649 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12649 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12649 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12649 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035881974279 : ℝ) * 12649 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003606425018 + 0.003307408500 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12649

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12649
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12649 BstLean.Part154.csC) (piBar (rhoBar 12649 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12649 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12649 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12649 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12649 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12649 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12649 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12649 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12649 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12649 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12649 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052591161610 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12649) ≤ 0.010618486946 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12649 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035881974279)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010618486946 + 2 * 0.737676 / 12649) := by gcongr
    _ ≤ (0.052591161610 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12649 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12649

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12649
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501252620 : ℝ) ≤ plow 12649 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12649) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849414481)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386135005) : eMP 12649 0.011 xi bn ≤ 0.001193270605 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12649 : ℝ) * (1 - 0.011))) ≤ 0.000589999283 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386135005 / (12649 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589999283 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589999283 : ℝ) + 3.141593 * 0.052849414481 / (12649 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193270605 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849414481)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386135005) : PiBarMP 12649 12 0.011 xi bn ≤ 0.161579253157 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12649 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037230834063 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.847489913721 : ℝ) ≤ √((12649 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.467773161915 : ℝ) ≤ √(12649 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12649) ≤ 0.123879115511 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037230834063 + 0.052849414481 * 1.772454 / (2 * (111.847489913721 : ℝ))) * (1 + 0.001193270605) +
        8 / (12649 * 112.467773161915) + 0.123879115511 := by gcongr
    _ ≤ (0.161579253157 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849414481)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386135005) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282481166789) :
    parallelOracle 12649 0.011 xi bn cd ≤ 0.162574193141 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12649 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12649 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501252620 : ℝ) ≤ plow 12649 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.467773161915 : ℝ) ≤ √(12649 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282481166789 : ℝ) / (2 * 0.560501252620 * 112.467773161915)) * 0.161579253157 +
        0.282481166789 ^ 2 / (2 * 0.560501252620 * 112.467773161915) := by gcongr
    _ ≤ (0.162574193141 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052849414481) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386135005)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282481166789) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12649 12649 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501252620 : ℝ) ≤ plow 12649 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.467773161915 : ℝ) ≤ √(12649 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12649 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12649 Θ 1.22 ≤ 0.011790937642 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.467773161915 := by gcongr <;> linarith
      _ ≤ (0.011790937642 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12649 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12649 12649 0.011 ≤ 0.008499208414 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12649 12649 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12649 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12649 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12649 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12649 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162574193141 + 0.011790937642 + (0.008499208414 : ℝ) *
        (1 + 2 * (0.282481166789 + 0.011790937642) / (0.560501252620 * 112.467773161915))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12649]

end BstLean.Part269.N12649

/-! The original eight local profiles supply actual 12649 moment certificates. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12649 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052849414481 ∧
    0 ≤ bN 12649 BstLean.Part154.csC (groupTheta g) ∧ bN 12649 BstLean.Part154.csC (groupTheta g) ≤ 0.001386135005 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12649 12649 0.011
      (momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12649 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12649 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12649 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229890005179 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12649 0.011
      (momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12649 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12649
/-! The actual computed-centre upper energy formula at 12649. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12649

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12649)
open BstLean.Part268 (cell12649)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085640421581
  | 2 => 0.086585962510
  | 3 => 0.087530055592
  | 4 => 0.088474213539
  | 5 => 0.089420262867
  | 6 => 0.090370390089
  | 7 => 0.091327192180
  | 8 => 0.092293731337
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12649 12649 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12649 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12649

/-! Actual upper energy certificates on all 43 source endpoints at 12649. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12649)
open BstLean.Part268 (cell12649)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12649 (gMinus 12649) (1 - (cell12649 i).lower) ≤ 1 ∧
    energyUpper 12649 (gMinus 12649) (BstLean.Part211.gPlus 12649)
      (finiteEnergy 12649 12649 0.011) (1 - (cell12649 i).lower) ≤
      (cell12649 i).energy := by
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
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨10,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨11,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨12,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨13,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨14,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨15,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨16,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨17,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨18,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨19,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨20,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨21,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨22,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨23,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨24,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨25,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨26,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨27,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨28,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨29,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨30,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨31,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨32,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨33,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨34,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨35,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨36,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨37,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨38,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨39,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨40,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨41,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨42,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨43,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨44,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨45,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨46,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨47,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨48,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨49,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨50,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨51,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12649) (by norm_num)
        (q := 1 - (cell12649 ⟨52,by decide⟩).lower)
        (by norm_num [cell12649]) (by norm_num [cell12649])
      exact ⟨E.1,E.2.trans (by norm_num [cell12649])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12649

/-! Source-cell containment and simple scalar guards at 12649. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12649)
open BstLean.Part268 (cell12649)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12649 ⟨10,by decide⟩).lower ∧ (cell12649 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12649 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12649 ⟨11,by decide⟩).lower ∧ (cell12649 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12649 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12649 ⟨12,by decide⟩).lower ∧ (cell12649 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12649 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12649 ⟨13,by decide⟩).lower ∧ (cell12649 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12649 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12649 ⟨14,by decide⟩).lower ∧ (cell12649 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12649 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12649 ⟨15,by decide⟩).lower ∧ (cell12649 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12649 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12649 ⟨16,by decide⟩).lower ∧ (cell12649 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12649 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12649 ⟨17,by decide⟩).lower ∧ (cell12649 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12649 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12649 ⟨18,by decide⟩).lower ∧ (cell12649 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12649 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12649 ⟨19,by decide⟩).lower ∧ (cell12649 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12649 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12649 ⟨20,by decide⟩).lower ∧ (cell12649 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12649 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12649 ⟨21,by decide⟩).lower ∧ (cell12649 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12649 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12649 ⟨22,by decide⟩).lower ∧ (cell12649 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12649 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12649 ⟨23,by decide⟩).lower ∧ (cell12649 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12649 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12649 ⟨24,by decide⟩).lower ∧ (cell12649 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12649 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12649 ⟨25,by decide⟩).lower ∧ (cell12649 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12649 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12649 ⟨26,by decide⟩).lower ∧ (cell12649 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12649 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12649 ⟨27,by decide⟩).lower ∧ (cell12649 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12649 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12649 ⟨28,by decide⟩).lower ∧ (cell12649 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12649 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12649 ⟨29,by decide⟩).lower ∧ (cell12649 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12649 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12649 ⟨30,by decide⟩).lower ∧ (cell12649 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12649 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12649 ⟨31,by decide⟩).lower ∧ (cell12649 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12649 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12649 ⟨32,by decide⟩).lower ∧ (cell12649 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12649 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12649 ⟨33,by decide⟩).lower ∧ (cell12649 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12649 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12649 ⟨34,by decide⟩).lower ∧ (cell12649 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12649 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12649 ⟨35,by decide⟩).lower ∧ (cell12649 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12649 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12649 ⟨36,by decide⟩).lower ∧ (cell12649 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12649 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12649 ⟨37,by decide⟩).lower ∧ (cell12649 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12649 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12649 ⟨38,by decide⟩).lower ∧ (cell12649 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12649 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12649 ⟨39,by decide⟩).lower ∧ (cell12649 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12649 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12649 ⟨40,by decide⟩).lower ∧ (cell12649 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12649 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12649 ⟨41,by decide⟩).lower ∧ (cell12649 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12649 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12649 ⟨42,by decide⟩).lower ∧ (cell12649 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12649 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12649 ⟨43,by decide⟩).lower ∧ (cell12649 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12649 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12649 ⟨44,by decide⟩).lower ∧ (cell12649 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12649 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12649 ⟨45,by decide⟩).lower ∧ (cell12649 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12649 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12649 ⟨46,by decide⟩).lower ∧ (cell12649 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12649 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12649 ⟨47,by decide⟩).lower ∧ (cell12649 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12649 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12649 ⟨48,by decide⟩).lower ∧ (cell12649 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12649 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12649 ⟨49,by decide⟩).lower ∧ (cell12649 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12649 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12649 ⟨50,by decide⟩).lower ∧ (cell12649 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12649 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12649 ⟨51,by decide⟩).lower ∧ (cell12649 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12649 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12649 ⟨52,by decide⟩).lower ∧ (cell12649 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12649 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12649 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12649 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12649,cell12649,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12649 i).lower ∧
    (cell12649 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12649 i).upper ≤ (0.532 : ℝ) ∧
    (cell12649 i).centre ≤ (0.1 : ℝ) ∧ (cell12649 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12649 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12649 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12649

/-! The local source numeric instances at 12649 have no network premises. -/
namespace BstLean.Part269.N12649
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12649)
open BstLean.Part268 (cell12649)

noncomputable def sourceNumerics12649 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12649 (cell12649 i)
      scalarRow12649.M scalarRow12649.H scalarRow12649.xi := by
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
    energy_allowance := scalarRow12649.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12649]
    centre_nonneg := (scalarRow12649.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12649])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12649