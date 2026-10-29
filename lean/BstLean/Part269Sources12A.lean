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
import BstLean.Part269Direction12
import BstLean.Part269Shared12
import BstLean.Part269Finite
import BstLean.Part269Rows12
import BstLean.Part269Source
/-! Actual 12650 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12650 ≤ (1.035880543492 : ℝ) := by
  have hr : (112.472218792019 : ℝ) ≤ √(12650 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.472218792019 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12650 12650 (11 / 1000) ≤
    (0.008498872467 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12650) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.472218792019 : ℝ) ≤ √(12650 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12650)
  have hdiv : K / √(12650 : ℝ) ≤ K / 112.472218792019 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.472218792019 ≤ (0.008498872467 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12650.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12650 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12650 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12650 := gPlus_lower 12650
end BstLean.Part269.N12650

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12650
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035880543491 : ℝ) ≤ wn 12650 := by
  have hn : √(12650 : ℝ) ≤ 112.472218792020 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12650 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.472218792020 ≤ 2 / √(12650 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252893858 : ℝ) ≤ rhoBar 12650 BstLean.Part154.csC ∧
    rhoBar 12650 BstLean.Part154.csC ≤ 0.000252894249 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035880543491 : ℝ) / (1.295212 * 12650) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035880543492 : ℝ) / (1.29521 * 12650) := by gcongr
      _ ≤ (0.000252894249 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12650 BstLean.Part154.csC) ≤ 0.001011640952 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12650 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) ≤ 0.000193162370 ∧
    cc1 (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) ≤ 0.000122910491 ∧
    cc2 (rhoBar 12650 BstLean.Part154.csC) ≤ 0.000071350473 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12650 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12650 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12650 BstLean.Part154.csC * nuR (rhoBar 12650 BstLean.Part154.csC)) ≤ 0.000505804487 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252894249 : ℝ) * 0.001011640952 := by gcongr
      _ ≤ (0.000505804487 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12650 BstLean.Part154.csC) * nuR (rhoBar 12650 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011640952 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12650 BstLean.Part154.csC) * rhoBar 12650 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252894249 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252894249 / 2 + 0.399 * 0.001011640952 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193162370 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505804487 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122910491 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252894249 / 1.414213562 := by gcongr
      _ ≤ (0.000071350473 : ℝ) := by norm_num

end BstLean.Part269.N12650

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12650
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) ≤ 1.61131E-7 := by
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12650 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12650 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12650 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193162370 : ℝ) ^ 2 + 0.000122910491 ^ 2 + 3 * 0.000071350473 ^ 2 +
        2 * 0.797885 * 0.000193162370 * 0.000122910491 + 2 * 0.000193162370 * 0.000071350473 +
        4 * 0.797885 * 0.000122910491 * 0.000071350473 := by gcongr
    _ ≤ (1.61131E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12650 BstLean.Part154.csC Θ ≤ 0.002640039884 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12650 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12650 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12650 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035880543492 * 1.61131E-7 / (0.000252893858 : ℝ) := by gcongr
    _ ≤ 0.002640039884 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12650 BstLean.Part154.csC Θ ≤ 0.002929474786 + 0.000667096764 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12650 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12650 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035880543492 : ℝ) * ((2 * Θ * 0.000252894249 +
        (6863 / 10000) * 0.000252894249 * 12650 * 0.001011640952) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002929474786 + 0.000667096764 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12650 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12650 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12650 0.011 Θ ∧ gammaRatio 12650 0.011 Θ ≤ 0.000086938504 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12650 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035880543492 : ℝ) * 0.525 / ((1 - 0.011) * 12650) := by gcongr
      _ ≤ (0.000086938504 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12650 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12650 0.011 Θ) :=
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
    badAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12650 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12650 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12650 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12650 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12650 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12650 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12650 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12650 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12650 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12650 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035880543492 : ℝ) * 12650 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003543786177 + 0.003307136648 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12650

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12650
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12650 BstLean.Part154.csC) (piBar (rhoBar 12650 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12650 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12650 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12650 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12650 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12650 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12650 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12650 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12650 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12650 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12650 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052589060279 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12650) ≤ 0.010618067234 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12650 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035880543492)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010618067234 + 2 * 0.737676 / 12650) := by gcongr
    _ ≤ (0.052589060279 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12650 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12650

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12650
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501298205 : ℝ) ≤ plow 12650 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12650) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786632918)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386020940) : eMP 12650 0.011 xi bn ≤ 0.001193158600 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12650 : ℝ) * (1 - 0.011))) ≤ 0.000589951688 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001386020940 / (12650 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589951688 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589951688 : ℝ) + 3.141593 * 0.052786632918 / (12650 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193158600 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786632918)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386020940) : PiBarMP 12650 12 0.011 xi bn ≤ 0.161572303451 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12650 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037229302170 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.851911025248 : ℝ) ≤ √((12650 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.472218792019 : ℝ) ≤ √(12650 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12650) ≤ 0.123874219007 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037229302170 + 0.052786632918 * 1.772454 / (2 * (111.851911025248 : ℝ))) * (1 + 0.001193158600) +
        8 / (12650 * 112.472218792019) + 0.123874219007 := by gcongr
    _ ≤ (0.161572303451 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786632918)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386020940) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282342477921) :
    parallelOracle 12650 0.011 xi bn cd ≤ 0.162566389427 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12650 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12650 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501298205 : ℝ) ≤ plow 12650 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.472218792019 : ℝ) ≤ √(12650 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282342477921 : ℝ) / (2 * 0.560501298205 * 112.472218792019)) * 0.161572303451 +
        0.282342477921 ^ 2 / (2 * 0.560501298205 * 112.472218792019) := by gcongr
    _ ≤ (0.162566389427 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786632918) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001386020940)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282342477921) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12650 12650 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501298205 : ℝ) ≤ plow 12650 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.472218792019 : ℝ) ≤ √(12650 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12650 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12650 Θ 1.22 ≤ 0.011790471588 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.472218792019 := by gcongr <;> linarith
      _ ≤ (0.011790471588 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12650 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12650 12650 0.011 ≤ 0.008498872467 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12650 12650 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12650 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12650 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12650 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12650 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162566389427 + 0.011790471588 + (0.008498872467 : ℝ) *
        (1 + 2 * (0.282342477921 + 0.011790471588) / (0.560501298205 * 112.472218792019))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12650]

end BstLean.Part269.N12650

/-! The original eight local profiles supply actual 12650 moment certificates. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12650 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052786632918 ∧
    0 ≤ bN 12650 BstLean.Part154.csC (groupTheta g) ∧ bN 12650 BstLean.Part154.csC (groupTheta g) ≤ 0.001386020940 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12650 12650 0.011
      (momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12650 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12650 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12650 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229753417642 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12650 0.011
      (momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12650 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12650
/-! The actual computed-centre upper energy formula at 12650. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12650

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12650)
open BstLean.Part268 (cell12650)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085637449117
  | 2 => 0.086582934144
  | 3 => 0.087526962964
  | 4 => 0.088471046376
  | 5 => 0.089417008650
  | 6 => 0.090367033678
  | 7 => 0.091323715394
  | 8 => 0.092290112488
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12650 12650 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12650 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12650

/-! Actual upper energy certificates on all 43 source endpoints at 12650. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12650)
open BstLean.Part268 (cell12650)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12650 (gMinus 12650) (1 - (cell12650 i).lower) ≤ 1 ∧
    energyUpper 12650 (gMinus 12650) (BstLean.Part211.gPlus 12650)
      (finiteEnergy 12650 12650 0.011) (1 - (cell12650 i).lower) ≤
      (cell12650 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨10,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨11,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨12,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨13,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨14,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨15,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨16,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨17,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨18,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨19,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨20,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨21,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨22,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨23,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨24,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨25,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨26,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨27,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨28,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨29,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨30,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨31,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨32,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨33,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨34,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨35,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨36,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨37,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨38,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨39,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨40,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨41,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨42,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨43,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨44,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨45,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨46,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨47,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨48,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨49,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨50,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨51,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12650) (by norm_num)
        (q := 1 - (cell12650 ⟨52,by decide⟩).lower)
        (by norm_num [cell12650]) (by norm_num [cell12650])
      exact ⟨E.1,E.2.trans (by norm_num [cell12650])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12650

/-! Source-cell containment and simple scalar guards at 12650. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12650)
open BstLean.Part268 (cell12650)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12650 ⟨10,by decide⟩).lower ∧ (cell12650 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12650 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12650 ⟨11,by decide⟩).lower ∧ (cell12650 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12650 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12650 ⟨12,by decide⟩).lower ∧ (cell12650 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12650 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12650 ⟨13,by decide⟩).lower ∧ (cell12650 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12650 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12650 ⟨14,by decide⟩).lower ∧ (cell12650 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12650 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12650 ⟨15,by decide⟩).lower ∧ (cell12650 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12650 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12650 ⟨16,by decide⟩).lower ∧ (cell12650 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12650 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12650 ⟨17,by decide⟩).lower ∧ (cell12650 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12650 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12650 ⟨18,by decide⟩).lower ∧ (cell12650 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12650 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12650 ⟨19,by decide⟩).lower ∧ (cell12650 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12650 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12650 ⟨20,by decide⟩).lower ∧ (cell12650 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12650 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12650 ⟨21,by decide⟩).lower ∧ (cell12650 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12650 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12650 ⟨22,by decide⟩).lower ∧ (cell12650 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12650 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12650 ⟨23,by decide⟩).lower ∧ (cell12650 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12650 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12650 ⟨24,by decide⟩).lower ∧ (cell12650 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12650 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12650 ⟨25,by decide⟩).lower ∧ (cell12650 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12650 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12650 ⟨26,by decide⟩).lower ∧ (cell12650 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12650 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12650 ⟨27,by decide⟩).lower ∧ (cell12650 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12650 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12650 ⟨28,by decide⟩).lower ∧ (cell12650 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12650 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12650 ⟨29,by decide⟩).lower ∧ (cell12650 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12650 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12650 ⟨30,by decide⟩).lower ∧ (cell12650 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12650 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12650 ⟨31,by decide⟩).lower ∧ (cell12650 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12650 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12650 ⟨32,by decide⟩).lower ∧ (cell12650 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12650 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12650 ⟨33,by decide⟩).lower ∧ (cell12650 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12650 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12650 ⟨34,by decide⟩).lower ∧ (cell12650 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12650 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12650 ⟨35,by decide⟩).lower ∧ (cell12650 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12650 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12650 ⟨36,by decide⟩).lower ∧ (cell12650 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12650 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12650 ⟨37,by decide⟩).lower ∧ (cell12650 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12650 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12650 ⟨38,by decide⟩).lower ∧ (cell12650 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12650 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12650 ⟨39,by decide⟩).lower ∧ (cell12650 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12650 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12650 ⟨40,by decide⟩).lower ∧ (cell12650 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12650 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12650 ⟨41,by decide⟩).lower ∧ (cell12650 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12650 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12650 ⟨42,by decide⟩).lower ∧ (cell12650 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12650 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12650 ⟨43,by decide⟩).lower ∧ (cell12650 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12650 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12650 ⟨44,by decide⟩).lower ∧ (cell12650 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12650 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12650 ⟨45,by decide⟩).lower ∧ (cell12650 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12650 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12650 ⟨46,by decide⟩).lower ∧ (cell12650 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12650 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12650 ⟨47,by decide⟩).lower ∧ (cell12650 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12650 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12650 ⟨48,by decide⟩).lower ∧ (cell12650 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12650 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12650 ⟨49,by decide⟩).lower ∧ (cell12650 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12650 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12650 ⟨50,by decide⟩).lower ∧ (cell12650 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12650 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12650 ⟨51,by decide⟩).lower ∧ (cell12650 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12650 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12650 ⟨52,by decide⟩).lower ∧ (cell12650 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12650 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12650 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12650 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12650,cell12650,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12650 i).lower ∧
    (cell12650 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12650 i).upper ≤ (0.532 : ℝ) ∧
    (cell12650 i).centre ≤ (0.1 : ℝ) ∧ (cell12650 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12650 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12650 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12650

/-! The local source numeric instances at 12650 have no network premises. -/
namespace BstLean.Part269.N12650
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12650)
open BstLean.Part268 (cell12650)

noncomputable def sourceNumerics12650 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12650 (cell12650 i)
      scalarRow12650.M scalarRow12650.H scalarRow12650.xi := by
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
    energy_allowance := scalarRow12650.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12650]
    centre_nonneg := (scalarRow12650.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12650])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12650
/-! Actual 12651 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12651 ≤ (1.035879112876 : ℝ) := by
  have hr : (112.476664246411 : ℝ) ≤ √(12651 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.476664246411 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12651 12651 (11 / 1000) ≤
    (0.008498536561 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12651) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.476664246411 : ℝ) ≤ √(12651 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12651)
  have hdiv : K / √(12651 : ℝ) ≤ K / 112.476664246411 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.476664246411 ≤ (0.008498536561 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12651.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12651 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12651 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12651 := gPlus_lower 12651
end BstLean.Part269.N12651

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12651
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035879112875 : ℝ) ≤ wn 12651 := by
  have hn : √(12651 : ℝ) ≤ 112.476664246412 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12651 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.476664246412 ≤ 2 / √(12651 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252873519 : ℝ) ≤ rhoBar 12651 BstLean.Part154.csC ∧
    rhoBar 12651 BstLean.Part154.csC ≤ 0.000252873910 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035879112875 : ℝ) / (1.295212 * 12651) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035879112876 : ℝ) / (1.29521 * 12651) := by gcongr
      _ ≤ (0.000252873910 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12651 BstLean.Part154.csC) ≤ 0.001011559586 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12651 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) ≤ 0.000193146834 ∧
    cc1 (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) ≤ 0.000122900606 ∧
    cc2 (rhoBar 12651 BstLean.Part154.csC) ≤ 0.000071344734 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12651 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12651 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12651 BstLean.Part154.csC * nuR (rhoBar 12651 BstLean.Part154.csC)) ≤ 0.000505763807 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252873910 : ℝ) * 0.001011559586 := by gcongr
      _ ≤ (0.000505763807 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12651 BstLean.Part154.csC) * nuR (rhoBar 12651 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011559586 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12651 BstLean.Part154.csC) * rhoBar 12651 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252873910 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252873910 / 2 + 0.399 * 0.001011559586 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193146834 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505763807 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122900606 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252873910 / 1.414213562 := by gcongr
      _ ≤ (0.000071344734 : ℝ) := by norm_num

end BstLean.Part269.N12651

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12651
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) ≤ 1.61106E-7 := by
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12651 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12651 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12651 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193146834 : ℝ) ^ 2 + 0.000122900606 ^ 2 + 3 * 0.000071344734 ^ 2 +
        2 * 0.797885 * 0.000193146834 * 0.000122900606 + 2 * 0.000193146834 * 0.000071344734 +
        4 * 0.797885 * 0.000122900606 * 0.000071344734 := by gcongr
    _ ≤ (1.61106E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12651 BstLean.Part154.csC Θ ≤ 0.002639838937 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12651 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12651 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12651 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035879112876 * 1.61106E-7 / (0.000252873519 : ℝ) := by gcongr
    _ ≤ 0.002639838937 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12651 BstLean.Part154.csC Θ ≤ 0.002929231081 + 0.000667042192 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12651 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12651 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035879112876 : ℝ) * ((2 * Θ * 0.000252873910 +
        (6863 / 10000) * 0.000252873910 * 12651 * 0.001011559586) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002929231081 + 0.000667042192 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12651 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12651 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12651 0.011 Θ ∧ gammaRatio 12651 0.011 Θ ≤ 0.000086931511 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12651 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035879112876 : ℝ) * 0.525 / ((1 - 0.011) * 12651) := by gcongr
      _ ≤ (0.000086931511 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12651 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12651 0.011 Θ) :=
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
    badAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12651 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12651 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12651 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12651 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12651 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12651 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12651 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12651 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12651 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12651 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035879112876 : ℝ) * 12651 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003543542472 + 0.003306881129 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12651

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12651
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12651 BstLean.Part154.csC) (piBar (rhoBar 12651 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12651 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12651 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12651 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12651 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12651 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12651 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12651 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12651 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12651 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12651 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052586959205 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12651) ≤ 0.010617647573 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12651 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035879112876)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010617647573 + 2 * 0.737676 / 12651) := by gcongr
    _ ≤ (0.052586959205 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12651 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12651

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12651
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501343783 : ℝ) ≤ plow 12651 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12651) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786255065)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385915442) : eMP 12651 0.011 xi bn ≤ 0.001193065920 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12651 : ℝ) * (1 - 0.011))) ≤ 0.000589905919 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385915442 / (12651 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589905919 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589905919 : ℝ) + 3.141593 * 0.052786255065 / (12651 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001193065920 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786255065)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385915442) : PiBarMP 12651 12 0.011 xi bn ≤ 0.161565965239 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12651 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037227885275 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.856331962030 : ℝ) ≤ √((12651 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.476664246411 : ℝ) ≤ √(12651 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12651) ≤ 0.123869323083 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037227885275 + 0.052786255065 * 1.772454 / (2 * (111.856331962030 : ℝ))) * (1 + 0.001193065920) +
        8 / (12651 * 112.476664246411) + 0.123869323083 := by gcongr
    _ ≤ (0.161565965239 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786255065)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385915442) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282339554544) :
    parallelOracle 12651 0.011 xi bn cd ≤ 0.162559980813 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12651 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12651 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501343783 : ℝ) ≤ plow 12651 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.476664246411 : ℝ) ≤ √(12651 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282339554544 : ℝ) / (2 * 0.560501343783 * 112.476664246411)) * 0.161565965239 +
        0.282339554544 ^ 2 / (2 * 0.560501343783 * 112.476664246411) := by gcongr
    _ ≤ (0.162559980813 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052786255065) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385915442)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282339554544) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12651 12651 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501343783 : ℝ) ≤ plow 12651 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.476664246411 : ℝ) ≤ √(12651 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12651 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12651 Θ 1.22 ≤ 0.011790005589 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.476664246411 := by gcongr <;> linarith
      _ ≤ (0.011790005589 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12651 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12651 12651 0.011 ≤ 0.008498536561 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12651 12651 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12651 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12651 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12651 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12651 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162559980813 + 0.011790005589 + (0.008498536561 : ℝ) *
        (1 + 2 * (0.282339554544 + 0.011790005589) / (0.560501343783 * 112.476664246411))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12651]

end BstLean.Part269.N12651

/-! The original eight local profiles supply actual 12651 moment certificates. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12651 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052786255065 ∧
    0 ≤ bN 12651 BstLean.Part154.csC (groupTheta g) ∧ bN 12651 BstLean.Part154.csC (groupTheta g) ≤ 0.001385915442 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12651 12651 0.011
      (momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12651 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12651 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12651 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229752595339 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12651 0.011
      (momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12651 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12651
/-! The actual computed-centre upper energy formula at 12651. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12651

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12651)
open BstLean.Part268 (cell12651)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085634477792
  | 2 => 0.086579906967
  | 3 => 0.087523871583
  | 4 => 0.088467880532
  | 5 => 0.089413755841
  | 6 => 0.090363678781
  | 7 => 0.091320240250
  | 8 => 0.092286495437
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12651 12651 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12651 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12651

/-! Actual upper energy certificates on all 43 source endpoints at 12651. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12651)
open BstLean.Part268 (cell12651)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12651 (gMinus 12651) (1 - (cell12651 i).lower) ≤ 1 ∧
    energyUpper 12651 (gMinus 12651) (BstLean.Part211.gPlus 12651)
      (finiteEnergy 12651 12651 0.011) (1 - (cell12651 i).lower) ≤
      (cell12651 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨10,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨11,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨12,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨13,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨14,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨15,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨16,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨17,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨18,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨19,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨20,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨21,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨22,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨23,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨24,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨25,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨26,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨27,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨28,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨29,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨30,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨31,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨32,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨33,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨34,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨35,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨36,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨37,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨38,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨39,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨40,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨41,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨42,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨43,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨44,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨45,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨46,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨47,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨48,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨49,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨50,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨51,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12651) (by norm_num)
        (q := 1 - (cell12651 ⟨52,by decide⟩).lower)
        (by norm_num [cell12651]) (by norm_num [cell12651])
      exact ⟨E.1,E.2.trans (by norm_num [cell12651])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12651

/-! Source-cell containment and simple scalar guards at 12651. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12651)
open BstLean.Part268 (cell12651)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12651 ⟨10,by decide⟩).lower ∧ (cell12651 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12651 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12651 ⟨11,by decide⟩).lower ∧ (cell12651 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12651 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12651 ⟨12,by decide⟩).lower ∧ (cell12651 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12651 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12651 ⟨13,by decide⟩).lower ∧ (cell12651 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12651 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12651 ⟨14,by decide⟩).lower ∧ (cell12651 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12651 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12651 ⟨15,by decide⟩).lower ∧ (cell12651 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12651 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12651 ⟨16,by decide⟩).lower ∧ (cell12651 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12651 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12651 ⟨17,by decide⟩).lower ∧ (cell12651 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12651 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12651 ⟨18,by decide⟩).lower ∧ (cell12651 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12651 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12651 ⟨19,by decide⟩).lower ∧ (cell12651 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12651 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12651 ⟨20,by decide⟩).lower ∧ (cell12651 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12651 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12651 ⟨21,by decide⟩).lower ∧ (cell12651 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12651 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12651 ⟨22,by decide⟩).lower ∧ (cell12651 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12651 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12651 ⟨23,by decide⟩).lower ∧ (cell12651 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12651 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12651 ⟨24,by decide⟩).lower ∧ (cell12651 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12651 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12651 ⟨25,by decide⟩).lower ∧ (cell12651 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12651 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12651 ⟨26,by decide⟩).lower ∧ (cell12651 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12651 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12651 ⟨27,by decide⟩).lower ∧ (cell12651 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12651 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12651 ⟨28,by decide⟩).lower ∧ (cell12651 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12651 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12651 ⟨29,by decide⟩).lower ∧ (cell12651 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12651 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12651 ⟨30,by decide⟩).lower ∧ (cell12651 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12651 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12651 ⟨31,by decide⟩).lower ∧ (cell12651 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12651 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12651 ⟨32,by decide⟩).lower ∧ (cell12651 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12651 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12651 ⟨33,by decide⟩).lower ∧ (cell12651 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12651 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12651 ⟨34,by decide⟩).lower ∧ (cell12651 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12651 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12651 ⟨35,by decide⟩).lower ∧ (cell12651 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12651 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12651 ⟨36,by decide⟩).lower ∧ (cell12651 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12651 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12651 ⟨37,by decide⟩).lower ∧ (cell12651 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12651 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12651 ⟨38,by decide⟩).lower ∧ (cell12651 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12651 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12651 ⟨39,by decide⟩).lower ∧ (cell12651 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12651 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12651 ⟨40,by decide⟩).lower ∧ (cell12651 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12651 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12651 ⟨41,by decide⟩).lower ∧ (cell12651 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12651 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12651 ⟨42,by decide⟩).lower ∧ (cell12651 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12651 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12651 ⟨43,by decide⟩).lower ∧ (cell12651 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12651 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12651 ⟨44,by decide⟩).lower ∧ (cell12651 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12651 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12651 ⟨45,by decide⟩).lower ∧ (cell12651 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12651 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12651 ⟨46,by decide⟩).lower ∧ (cell12651 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12651 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12651 ⟨47,by decide⟩).lower ∧ (cell12651 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12651 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12651 ⟨48,by decide⟩).lower ∧ (cell12651 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12651 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12651 ⟨49,by decide⟩).lower ∧ (cell12651 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12651 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12651 ⟨50,by decide⟩).lower ∧ (cell12651 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12651 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12651 ⟨51,by decide⟩).lower ∧ (cell12651 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12651 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12651 ⟨52,by decide⟩).lower ∧ (cell12651 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12651 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12651 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12651 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12651,cell12651,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12651 i).lower ∧
    (cell12651 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12651 i).upper ≤ (0.532 : ℝ) ∧
    (cell12651 i).centre ≤ (0.1 : ℝ) ∧ (cell12651 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12651 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12651 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12651

/-! The local source numeric instances at 12651 have no network premises. -/
namespace BstLean.Part269.N12651
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12651)
open BstLean.Part268 (cell12651)

noncomputable def sourceNumerics12651 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12651 (cell12651 i)
      scalarRow12651.M scalarRow12651.H scalarRow12651.xi := by
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
    energy_allowance := scalarRow12651.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12651]
    centre_nonneg := (scalarRow12651.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12651])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12651
/-! Actual 12652 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12652 ≤ (1.035877682430 : ℝ) := by
  have hr : (112.481109525110 : ℝ) ≤ √(12652 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.481109525110 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12652 12652 (11 / 1000) ≤
    (0.008498200694 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12652) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.481109525110 : ℝ) ≤ √(12652 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12652)
  have hdiv : K / √(12652 : ℝ) ≤ K / 112.481109525110 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.481109525110 ≤ (0.008498200694 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12652.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12652 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12652 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12652 := gPlus_lower 12652
end BstLean.Part269.N12652

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12652
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035877682429 : ℝ) ≤ wn 12652 := by
  have hn : √(12652 : ℝ) ≤ 112.481109525111 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12652 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.481109525111 ≤ 2 / √(12652 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252853183 : ℝ) ≤ rhoBar 12652 BstLean.Part154.csC ∧
    rhoBar 12652 BstLean.Part154.csC ≤ 0.000252853574 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035877682429 : ℝ) / (1.295212 * 12652) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035877682430 : ℝ) / (1.29521 * 12652) := by gcongr
      _ ≤ (0.000252853574 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12652 BstLean.Part154.csC) ≤ 0.001011478231 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12652 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) ≤ 0.000193131300 ∧
    cc1 (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) ≤ 0.000122890722 ∧
    cc2 (rhoBar 12652 BstLean.Part154.csC) ≤ 0.000071338997 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12652 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12652 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12652 BstLean.Part154.csC * nuR (rhoBar 12652 BstLean.Part154.csC)) ≤ 0.000505723132 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252853574 : ℝ) * 0.001011478231 := by gcongr
      _ ≤ (0.000505723132 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12652 BstLean.Part154.csC) * nuR (rhoBar 12652 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011478231 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12652 BstLean.Part154.csC) * rhoBar 12652 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252853574 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252853574 / 2 + 0.399 * 0.001011478231 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193131300 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505723132 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122890722 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252853574 / 1.414213562 := by gcongr
      _ ≤ (0.000071338997 : ℝ) := by norm_num

end BstLean.Part269.N12652

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12652
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) ≤ 1.61080E-7 := by
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12652 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12652 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12652 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193131300 : ℝ) ^ 2 + 0.000122890722 ^ 2 + 3 * 0.000071338997 ^ 2 +
        2 * 0.797885 * 0.000193131300 * 0.000122890722 + 2 * 0.000193131300 * 0.000071338997 +
        4 * 0.797885 * 0.000122890722 * 0.000071338997 := by gcongr
    _ ≤ (1.61080E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12652 BstLean.Part154.csC Θ ≤ 0.002639621541 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12652 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12652 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12652 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035877682430 * 1.61080E-7 / (0.000252853183 : ℝ) := by gcongr
    _ ≤ 0.002639621541 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12652 BstLean.Part154.csC Θ ≤ 0.002928987408 + 0.000666987628 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12652 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12652 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035877682430 : ℝ) * ((2 * Θ * 0.000252853574 +
        (6863 / 10000) * 0.000252853574 * 12652 * 0.001011478231) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002928987408 + 0.000666987628 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12652 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12652 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12652 0.011 Θ ∧ gammaRatio 12652 0.011 Θ ≤ 0.000086924520 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12652 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035877682430 : ℝ) * 0.525 / ((1 - 0.011) * 12652) := by gcongr
      _ ≤ (0.000086924520 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12652 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12652 0.011 Θ) :=
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
    badAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12652 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12652 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12652 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12652 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12652 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12652 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12652 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12652 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12652 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12652 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035877682430 : ℝ) * 12652 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003543298799 + 0.003306609169 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12652

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12652
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12652 BstLean.Part154.csC) (piBar (rhoBar 12652 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12652 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12652 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12652 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12652 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12652 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12652 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12652 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12652 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12652 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12652 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052584858378 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12652) ≤ 0.010617227961 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12652 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035877682430)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010617227961 + 2 * 0.737676 / 12652) := by gcongr
    _ ≤ (0.052584858378 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12652 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12652

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12652
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501389353 : ℝ) ≤ plow 12652 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12652) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785868613)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385801310) : eMP 12652 0.011 xi bn ≤ 0.001192969571 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12652 : ℝ) * (1 - 0.011))) ≤ 0.000589858317 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385801310 / (12652 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589858317 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589858317 : ℝ) + 3.141593 * 0.052785868613 / (12652 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192969571 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785868613)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385801310) : PiBarMP 12652 12 0.011 xi bn ≤ 0.161559511244 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12652 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037226352360 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.860752724089 : ℝ) ≤ √((12652 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.481109525110 : ℝ) ≤ √(12652 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12652) ≤ 0.123864427739 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037226352360 + 0.052785868613 * 1.772454 / (2 * (111.860752724089 : ℝ))) * (1 + 0.001192969571) +
        8 / (12652 * 112.481109525110) + 0.123864427739 := by gcongr
    _ ≤ (0.161559511244 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785868613)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385801310) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282336612698) :
    parallelOracle 12652 0.011 xi bn cd ≤ 0.162553456059 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12652 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12652 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501389353 : ℝ) ≤ plow 12652 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.481109525110 : ℝ) ≤ √(12652 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282336612698 : ℝ) / (2 * 0.560501389353 * 112.481109525110)) * 0.161559511244 +
        0.282336612698 ^ 2 / (2 * 0.560501389353 * 112.481109525110) := by gcongr
    _ ≤ (0.162553456059 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785868613) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385801310)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282336612698) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12652 12652 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501389353 : ℝ) ≤ plow 12652 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.481109525110 : ℝ) ≤ √(12652 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12652 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12652 Θ 1.22 ≤ 0.011789539645 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.481109525110 := by gcongr <;> linarith
      _ ≤ (0.011789539645 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12652 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12652 12652 0.011 ≤ 0.008498200694 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12652 12652 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12652 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12652 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12652 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12652 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162553456059 + 0.011789539645 + (0.008498200694 : ℝ) *
        (1 + 2 * (0.282336612698 + 0.011789539645) / (0.560501389353 * 112.481109525110))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12652]

end BstLean.Part269.N12652

/-! The original eight local profiles supply actual 12652 moment certificates. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12652 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052785868613 ∧
    0 ≤ bN 12652 BstLean.Part154.csC (groupTheta g) ∧ bN 12652 BstLean.Part154.csC (groupTheta g) ≤ 0.001385801310 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12652 12652 0.011
      (momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12652 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12652 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12652 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229751754320 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12652 0.011
      (momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12652 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12652
/-! The actual computed-centre upper energy formula at 12652. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12652

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12652)
open BstLean.Part268 (cell12652)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085631507608
  | 2 => 0.086576880977
  | 3 => 0.087520781448
  | 4 => 0.088464716006
  | 5 => 0.089410504436
  | 6 => 0.090360325396
  | 7 => 0.091316766748
  | 8 => 0.092282880183
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12652 12652 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12652 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12652

/-! Actual upper energy certificates on all 43 source endpoints at 12652. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12652)
open BstLean.Part268 (cell12652)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12652 (gMinus 12652) (1 - (cell12652 i).lower) ≤ 1 ∧
    energyUpper 12652 (gMinus 12652) (BstLean.Part211.gPlus 12652)
      (finiteEnergy 12652 12652 0.011) (1 - (cell12652 i).lower) ≤
      (cell12652 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨10,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨11,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨12,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨13,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨14,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨15,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨16,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨17,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨18,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨19,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨20,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨21,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨22,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨23,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨24,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨25,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨26,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨27,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨28,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨29,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨30,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨31,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨32,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨33,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨34,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨35,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨36,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨37,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨38,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨39,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨40,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨41,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨42,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨43,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨44,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨45,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨46,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨47,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨48,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨49,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨50,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨51,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12652) (by norm_num)
        (q := 1 - (cell12652 ⟨52,by decide⟩).lower)
        (by norm_num [cell12652]) (by norm_num [cell12652])
      exact ⟨E.1,E.2.trans (by norm_num [cell12652])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12652

/-! Source-cell containment and simple scalar guards at 12652. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12652)
open BstLean.Part268 (cell12652)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12652 ⟨10,by decide⟩).lower ∧ (cell12652 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12652 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12652 ⟨11,by decide⟩).lower ∧ (cell12652 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12652 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12652 ⟨12,by decide⟩).lower ∧ (cell12652 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12652 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12652 ⟨13,by decide⟩).lower ∧ (cell12652 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12652 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12652 ⟨14,by decide⟩).lower ∧ (cell12652 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12652 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12652 ⟨15,by decide⟩).lower ∧ (cell12652 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12652 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12652 ⟨16,by decide⟩).lower ∧ (cell12652 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12652 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12652 ⟨17,by decide⟩).lower ∧ (cell12652 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12652 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12652 ⟨18,by decide⟩).lower ∧ (cell12652 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12652 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12652 ⟨19,by decide⟩).lower ∧ (cell12652 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12652 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12652 ⟨20,by decide⟩).lower ∧ (cell12652 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12652 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12652 ⟨21,by decide⟩).lower ∧ (cell12652 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12652 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12652 ⟨22,by decide⟩).lower ∧ (cell12652 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12652 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12652 ⟨23,by decide⟩).lower ∧ (cell12652 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12652 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12652 ⟨24,by decide⟩).lower ∧ (cell12652 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12652 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12652 ⟨25,by decide⟩).lower ∧ (cell12652 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12652 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12652 ⟨26,by decide⟩).lower ∧ (cell12652 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12652 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12652 ⟨27,by decide⟩).lower ∧ (cell12652 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12652 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12652 ⟨28,by decide⟩).lower ∧ (cell12652 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12652 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12652 ⟨29,by decide⟩).lower ∧ (cell12652 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12652 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12652 ⟨30,by decide⟩).lower ∧ (cell12652 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12652 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12652 ⟨31,by decide⟩).lower ∧ (cell12652 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12652 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12652 ⟨32,by decide⟩).lower ∧ (cell12652 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12652 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12652 ⟨33,by decide⟩).lower ∧ (cell12652 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12652 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12652 ⟨34,by decide⟩).lower ∧ (cell12652 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12652 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12652 ⟨35,by decide⟩).lower ∧ (cell12652 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12652 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12652 ⟨36,by decide⟩).lower ∧ (cell12652 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12652 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12652 ⟨37,by decide⟩).lower ∧ (cell12652 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12652 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12652 ⟨38,by decide⟩).lower ∧ (cell12652 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12652 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12652 ⟨39,by decide⟩).lower ∧ (cell12652 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12652 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12652 ⟨40,by decide⟩).lower ∧ (cell12652 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12652 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12652 ⟨41,by decide⟩).lower ∧ (cell12652 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12652 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12652 ⟨42,by decide⟩).lower ∧ (cell12652 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12652 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12652 ⟨43,by decide⟩).lower ∧ (cell12652 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12652 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12652 ⟨44,by decide⟩).lower ∧ (cell12652 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12652 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12652 ⟨45,by decide⟩).lower ∧ (cell12652 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12652 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12652 ⟨46,by decide⟩).lower ∧ (cell12652 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12652 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12652 ⟨47,by decide⟩).lower ∧ (cell12652 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12652 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12652 ⟨48,by decide⟩).lower ∧ (cell12652 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12652 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12652 ⟨49,by decide⟩).lower ∧ (cell12652 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12652 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12652 ⟨50,by decide⟩).lower ∧ (cell12652 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12652 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12652 ⟨51,by decide⟩).lower ∧ (cell12652 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12652 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12652 ⟨52,by decide⟩).lower ∧ (cell12652 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12652 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12652 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12652 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12652,cell12652,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12652 i).lower ∧
    (cell12652 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12652 i).upper ≤ (0.532 : ℝ) ∧
    (cell12652 i).centre ≤ (0.1 : ℝ) ∧ (cell12652 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12652 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12652 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12652

/-! The local source numeric instances at 12652 have no network premises. -/
namespace BstLean.Part269.N12652
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12652)
open BstLean.Part268 (cell12652)

noncomputable def sourceNumerics12652 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12652 (cell12652 i)
      scalarRow12652.M scalarRow12652.H scalarRow12652.xi := by
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
    energy_allowance := scalarRow12652.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12652]
    centre_nonneg := (scalarRow12652.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12652])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12652
/-! Actual 12653 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12653 ≤ (1.035876252155 : ℝ) := by
  have hr : (112.485554628138 : ℝ) ≤ √(12653 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.485554628138 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12653 12653 (11 / 1000) ≤
    (0.008497864867 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12653) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.485554628138 : ℝ) ≤ √(12653 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12653)
  have hdiv : K / √(12653 : ℝ) ≤ K / 112.485554628138 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.485554628138 ≤ (0.008497864867 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12653.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12653 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12653 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12653 := gPlus_lower 12653
end BstLean.Part269.N12653

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12653
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035876252154 : ℝ) ≤ wn 12653 := by
  have hn : √(12653 : ℝ) ≤ 112.485554628139 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12653 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.485554628139 ≤ 2 / √(12653 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252832850 : ℝ) ≤ rhoBar 12653 BstLean.Part154.csC ∧
    rhoBar 12653 BstLean.Part154.csC ≤ 0.000252833241 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035876252154 : ℝ) / (1.295212 * 12653) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035876252155 : ℝ) / (1.29521 * 12653) := by gcongr
      _ ≤ (0.000252833241 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12653 BstLean.Part154.csC) ≤ 0.001011396889 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12653 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) ≤ 0.000193115769 ∧
    cc1 (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) ≤ 0.000122880839 ∧
    cc2 (rhoBar 12653 BstLean.Part154.csC) ≤ 0.000071333260 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12653 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12653 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12653 BstLean.Part154.csC * nuR (rhoBar 12653 BstLean.Part154.csC)) ≤ 0.000505682463 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252833241 : ℝ) * 0.001011396889 := by gcongr
      _ ≤ (0.000505682463 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12653 BstLean.Part154.csC) * nuR (rhoBar 12653 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011396889 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12653 BstLean.Part154.csC) * rhoBar 12653 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252833241 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252833241 / 2 + 0.399 * 0.001011396889 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193115769 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505682463 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122880839 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252833241 / 1.414213562 := by gcongr
      _ ≤ (0.000071333260 : ℝ) := by norm_num

end BstLean.Part269.N12653

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12653
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) ≤ 1.61054E-7 := by
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12653 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12653 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12653 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193115769 : ℝ) ^ 2 + 0.000122880839 ^ 2 + 3 * 0.000071333260 ^ 2 +
        2 * 0.797885 * 0.000193115769 * 0.000122880839 + 2 * 0.000193115769 * 0.000071333260 +
        4 * 0.797885 * 0.000122880839 * 0.000071333260 := by gcongr
    _ ≤ (1.61054E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12653 BstLean.Part154.csC Θ ≤ 0.002639404080 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12653 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12653 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12653 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035876252155 * 1.61054E-7 / (0.000252832850 : ℝ) := by gcongr
    _ ≤ 0.002639404080 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12653 BstLean.Part154.csC Θ ≤ 0.002928743772 + 0.000666933072 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12653 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12653 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035876252155 : ℝ) * ((2 * Θ * 0.000252833241 +
        (6863 / 10000) * 0.000252833241 * 12653 * 0.001011396889) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002928743772 + 0.000666933072 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12653 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12653 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12653 0.011 Θ ∧ gammaRatio 12653 0.011 Θ ≤ 0.000086917531 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12653 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035876252155 : ℝ) * 0.525 / ((1 - 0.011) * 12653) := by gcongr
      _ ≤ (0.000086917531 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12653 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12653 0.011 Θ) :=
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
    badAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12653 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12653 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12653 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12653 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12653 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12653 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12653 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12653 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12653 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12653 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035876252155 : ℝ) * 12653 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003543055163 + 0.003306337152 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12653

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12653
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12653 BstLean.Part154.csC) (piBar (rhoBar 12653 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12653 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12653 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12653 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12653 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12653 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12653 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12653 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12653 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12653 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12653 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052582757803 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12653) ≤ 0.010616808399 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12653 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035876252155)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010616808399 + 2 * 0.737676 / 12653) := by gcongr
    _ ≤ (0.052582757803 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12653 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12653

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12653
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501434916 : ℝ) ≤ plow 12653 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12653) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785482168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385687142) : eMP 12653 0.011 xi bn ≤ 0.001192873213 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12653 : ℝ) * (1 - 0.011))) ≤ 0.000589810710 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385687142 / (12653 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589810710 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589810710 : ℝ) + 3.141593 * 0.052785482168 / (12653 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192873213 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785482168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385687142) : PiBarMP 12653 12 0.011 xi bn ≤ 0.161553057286 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12653 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037224818899 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.865173311446 : ℝ) ≤ √((12653 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.485554628138 : ℝ) ≤ √(12653 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12653) ≤ 0.123859532976 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037224818899 + 0.052785482168 * 1.772454 / (2 * (111.865173311446 : ℝ))) * (1 + 0.001192873213) +
        8 / (12653 * 112.485554628138) + 0.123859532976 := by gcongr
    _ ≤ (0.161553057286 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785482168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385687142) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282333671116) :
    parallelOracle 12653 0.011 xi bn cd ≤ 0.162546931350 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12653 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12653 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501434916 : ℝ) ≤ plow 12653 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.485554628138 : ℝ) ≤ √(12653 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282333671116 : ℝ) / (2 * 0.560501434916 * 112.485554628138)) * 0.161553057286 +
        0.282333671116 ^ 2 / (2 * 0.560501434916 * 112.485554628138) := by gcongr
    _ ≤ (0.162546931350 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785482168) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385687142)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282333671116) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12653 12653 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501434916 : ℝ) ≤ plow 12653 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.485554628138 : ℝ) ≤ √(12653 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12653 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12653 Θ 1.22 ≤ 0.011789073757 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.485554628138 := by gcongr <;> linarith
      _ ≤ (0.011789073757 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12653 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12653 12653 0.011 ≤ 0.008497864867 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12653 12653 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12653 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12653 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12653 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12653 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162546931350 + 0.011789073757 + (0.008497864867 : ℝ) *
        (1 + 2 * (0.282333671116 + 0.011789073757) / (0.560501434916 * 112.485554628138))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12653]

end BstLean.Part269.N12653

/-! The original eight local profiles supply actual 12653 moment certificates. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12653 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052785482168 ∧
    0 ≤ bN 12653 BstLean.Part154.csC (groupTheta g) ∧ bN 12653 BstLean.Part154.csC (groupTheta g) ≤ 0.001385687142 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12653 12653 0.011
      (momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12653 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12653 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12653 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229750913313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12653 0.011
      (momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12653 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12653
/-! The actual computed-centre upper energy formula at 12653. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12653

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12653)
open BstLean.Part268 (cell12653)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085628538562
  | 2 => 0.086573856172
  | 3 => 0.087517692557
  | 4 => 0.088461552795
  | 5 => 0.089407254436
  | 6 => 0.090356973522
  | 7 => 0.091313294886
  | 8 => 0.092279266723
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12653 12653 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12653 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12653

/-! Actual upper energy certificates on all 43 source endpoints at 12653. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12653)
open BstLean.Part268 (cell12653)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12653 (gMinus 12653) (1 - (cell12653 i).lower) ≤ 1 ∧
    energyUpper 12653 (gMinus 12653) (BstLean.Part211.gPlus 12653)
      (finiteEnergy 12653 12653 0.011) (1 - (cell12653 i).lower) ≤
      (cell12653 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨10,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨11,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨12,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨13,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨14,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨15,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨16,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨17,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨18,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨19,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨20,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨21,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨22,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨23,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨24,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨25,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨26,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨27,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨28,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨29,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨30,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨31,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨32,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨33,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨34,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨35,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨36,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨37,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨38,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨39,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨40,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨41,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨42,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨43,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨44,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨45,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨46,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨47,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨48,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨49,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨50,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨51,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12653) (by norm_num)
        (q := 1 - (cell12653 ⟨52,by decide⟩).lower)
        (by norm_num [cell12653]) (by norm_num [cell12653])
      exact ⟨E.1,E.2.trans (by norm_num [cell12653])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12653

/-! Source-cell containment and simple scalar guards at 12653. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12653)
open BstLean.Part268 (cell12653)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12653 ⟨10,by decide⟩).lower ∧ (cell12653 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12653 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12653 ⟨11,by decide⟩).lower ∧ (cell12653 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12653 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12653 ⟨12,by decide⟩).lower ∧ (cell12653 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12653 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12653 ⟨13,by decide⟩).lower ∧ (cell12653 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12653 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12653 ⟨14,by decide⟩).lower ∧ (cell12653 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12653 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12653 ⟨15,by decide⟩).lower ∧ (cell12653 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12653 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12653 ⟨16,by decide⟩).lower ∧ (cell12653 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12653 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12653 ⟨17,by decide⟩).lower ∧ (cell12653 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12653 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12653 ⟨18,by decide⟩).lower ∧ (cell12653 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12653 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12653 ⟨19,by decide⟩).lower ∧ (cell12653 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12653 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12653 ⟨20,by decide⟩).lower ∧ (cell12653 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12653 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12653 ⟨21,by decide⟩).lower ∧ (cell12653 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12653 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12653 ⟨22,by decide⟩).lower ∧ (cell12653 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12653 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12653 ⟨23,by decide⟩).lower ∧ (cell12653 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12653 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12653 ⟨24,by decide⟩).lower ∧ (cell12653 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12653 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12653 ⟨25,by decide⟩).lower ∧ (cell12653 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12653 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12653 ⟨26,by decide⟩).lower ∧ (cell12653 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12653 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12653 ⟨27,by decide⟩).lower ∧ (cell12653 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12653 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12653 ⟨28,by decide⟩).lower ∧ (cell12653 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12653 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12653 ⟨29,by decide⟩).lower ∧ (cell12653 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12653 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12653 ⟨30,by decide⟩).lower ∧ (cell12653 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12653 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12653 ⟨31,by decide⟩).lower ∧ (cell12653 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12653 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12653 ⟨32,by decide⟩).lower ∧ (cell12653 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12653 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12653 ⟨33,by decide⟩).lower ∧ (cell12653 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12653 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12653 ⟨34,by decide⟩).lower ∧ (cell12653 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12653 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12653 ⟨35,by decide⟩).lower ∧ (cell12653 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12653 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12653 ⟨36,by decide⟩).lower ∧ (cell12653 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12653 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12653 ⟨37,by decide⟩).lower ∧ (cell12653 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12653 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12653 ⟨38,by decide⟩).lower ∧ (cell12653 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12653 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12653 ⟨39,by decide⟩).lower ∧ (cell12653 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12653 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12653 ⟨40,by decide⟩).lower ∧ (cell12653 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12653 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12653 ⟨41,by decide⟩).lower ∧ (cell12653 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12653 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12653 ⟨42,by decide⟩).lower ∧ (cell12653 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12653 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12653 ⟨43,by decide⟩).lower ∧ (cell12653 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12653 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12653 ⟨44,by decide⟩).lower ∧ (cell12653 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12653 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12653 ⟨45,by decide⟩).lower ∧ (cell12653 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12653 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12653 ⟨46,by decide⟩).lower ∧ (cell12653 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12653 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12653 ⟨47,by decide⟩).lower ∧ (cell12653 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12653 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12653 ⟨48,by decide⟩).lower ∧ (cell12653 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12653 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12653 ⟨49,by decide⟩).lower ∧ (cell12653 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12653 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12653 ⟨50,by decide⟩).lower ∧ (cell12653 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12653 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12653 ⟨51,by decide⟩).lower ∧ (cell12653 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12653 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12653 ⟨52,by decide⟩).lower ∧ (cell12653 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12653 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12653 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12653 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12653,cell12653,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12653 i).lower ∧
    (cell12653 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12653 i).upper ≤ (0.532 : ℝ) ∧
    (cell12653 i).centre ≤ (0.1 : ℝ) ∧ (cell12653 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12653 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12653 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12653

/-! The local source numeric instances at 12653 have no network premises. -/
namespace BstLean.Part269.N12653
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12653)
open BstLean.Part268 (cell12653)

noncomputable def sourceNumerics12653 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12653 (cell12653 i)
      scalarRow12653.M scalarRow12653.H scalarRow12653.xi := by
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
    energy_allowance := scalarRow12653.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12653]
    centre_nonneg := (scalarRow12653.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12653])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12653
/-! Actual 12654 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12654 ≤ (1.035874822051 : ℝ) := by
  have hr : (112.489999555516 : ℝ) ≤ √(12654 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.489999555516 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12654 12654 (11 / 1000) ≤
    (0.008497529080 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12654) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.489999555516 : ℝ) ≤ √(12654 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12654)
  have hdiv : K / √(12654 : ℝ) ≤ K / 112.489999555516 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.489999555516 ≤ (0.008497529080 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12654.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12654 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12654 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12654 := gPlus_lower 12654
end BstLean.Part269.N12654

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12654
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035874822050 : ℝ) ≤ wn 12654 := by
  have hn : √(12654 : ℝ) ≤ 112.489999555517 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12654 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.489999555517 ≤ 2 / √(12654 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252812520 : ℝ) ≤ rhoBar 12654 BstLean.Part154.csC ∧
    rhoBar 12654 BstLean.Part154.csC ≤ 0.000252812912 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035874822050 : ℝ) / (1.295212 * 12654) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035874822051 : ℝ) / (1.29521 * 12654) := by gcongr
      _ ≤ (0.000252812912 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12654 BstLean.Part154.csC) ≤ 0.001011315563 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12654 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) ≤ 0.000193100241 ∧
    cc1 (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) ≤ 0.000122870959 ∧
    cc2 (rhoBar 12654 BstLean.Part154.csC) ≤ 0.000071327525 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12654 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12654 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12654 BstLean.Part154.csC * nuR (rhoBar 12654 BstLean.Part154.csC)) ≤ 0.000505641803 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252812912 : ℝ) * 0.001011315563 := by gcongr
      _ ≤ (0.000505641803 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12654 BstLean.Part154.csC) * nuR (rhoBar 12654 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011315563 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12654 BstLean.Part154.csC) * rhoBar 12654 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252812912 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252812912 / 2 + 0.399 * 0.001011315563 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193100241 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505641803 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122870959 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252812912 / 1.414213562 := by gcongr
      _ ≤ (0.000071327525 : ℝ) := by norm_num

end BstLean.Part269.N12654

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12654
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) ≤ 1.61028E-7 := by
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12654 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12654 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12654 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193100241 : ℝ) ^ 2 + 0.000122870959 ^ 2 + 3 * 0.000071327525 ^ 2 +
        2 * 0.797885 * 0.000193100241 * 0.000122870959 + 2 * 0.000193100241 * 0.000071327525 +
        4 * 0.797885 * 0.000122870959 * 0.000071327525 := by gcongr
    _ ≤ (1.61028E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12654 BstLean.Part154.csC Θ ≤ 0.002639186554 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12654 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12654 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12654 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035874822051 * 1.61028E-7 / (0.000252812520 : ℝ) := by gcongr
    _ ≤ 0.002639186554 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12654 BstLean.Part154.csC Θ ≤ 0.002928500193 + 0.000666878526 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12654 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12654 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035874822051 : ℝ) * ((2 * Θ * 0.000252812912 +
        (6863 / 10000) * 0.000252812912 * 12654 * 0.001011315563) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002928500193 + 0.000666878526 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12654 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12654 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12654 0.011 Θ ∧ gammaRatio 12654 0.011 Θ ≤ 0.000086910542 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12654 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035874822051 : ℝ) * 0.525 / ((1 - 0.011) * 12654) := by gcongr
      _ ≤ (0.000086910542 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12654 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12654 0.011 Θ) :=
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
    badAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12654 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12654 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12654 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12654 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12654 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12654 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12654 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12654 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12654 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12654 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035874822051 : ℝ) * 12654 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003542811584 + 0.003306065080 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12654

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12654
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12654 BstLean.Part154.csC) (piBar (rhoBar 12654 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12654 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12654 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12654 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12654 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12654 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12654 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12654 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12654 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12654 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12654 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052580657475 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12654) ≤ 0.010616388886 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12654 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035874822051)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010616388886 + 2 * 0.737676 / 12654) := by gcongr
    _ ≤ (0.052580657475 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12654 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12654

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12654
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501480472 : ℝ) ≤ plow 12654 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12654) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785095751)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385572941) : eMP 12654 0.011 xi bn ≤ 0.001192776848 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12654 : ℝ) * (1 - 0.011))) ≤ 0.000589763100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385572941 / (12654 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589763100 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589763100 : ℝ) + 3.141593 * 0.052785095751 / (12654 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192776848 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785095751)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385572941) : PiBarMP 12654 12 0.011 xi bn ≤ 0.161546603403 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12654 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037223284931 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.869593724121 : ℝ) ≤ √((12654 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.489999555516 : ℝ) ≤ √(12654 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12654) ≤ 0.123854638793 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037223284931 + 0.052785095751 * 1.772454 / (2 * (111.869593724121 : ℝ))) * (1 + 0.001192776848) +
        8 / (12654 * 112.489999555516) + 0.123854638793 := by gcongr
    _ ≤ (0.161546603403 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785095751)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385572941) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282330729839) :
    parallelOracle 12654 0.011 xi bn cd ≤ 0.162540406726 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12654 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12654 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501480472 : ℝ) ≤ plow 12654 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.489999555516 : ℝ) ≤ √(12654 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282330729839 : ℝ) / (2 * 0.560501480472 * 112.489999555516)) * 0.161546603403 +
        0.282330729839 ^ 2 / (2 * 0.560501480472 * 112.489999555516) := by gcongr
    _ ≤ (0.162540406726 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052785095751) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385572941)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282330729839) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12654 12654 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501480472 : ℝ) ≤ plow 12654 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.489999555516 : ℝ) ≤ √(12654 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12654 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12654 Θ 1.22 ≤ 0.011788607923 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.489999555516 := by gcongr <;> linarith
      _ ≤ (0.011788607923 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12654 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12654 12654 0.011 ≤ 0.008497529080 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12654 12654 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12654 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12654 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12654 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12654 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162540406726 + 0.011788607923 + (0.008497529080 : ℝ) *
        (1 + 2 * (0.282330729839 + 0.011788607923) / (0.560501480472 * 112.489999555516))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12654]

end BstLean.Part269.N12654

/-! The original eight local profiles supply actual 12654 moment certificates. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12654 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052785095751 ∧
    0 ≤ bN 12654 BstLean.Part154.csC (groupTheta g) ∧ bN 12654 BstLean.Part154.csC (groupTheta g) ≤ 0.001385572941 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12654 12654 0.011
      (momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12654 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12654 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12654 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229750072364 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12654 0.011
      (momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12654 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12654
/-! The actual computed-centre upper energy formula at 12654. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12654

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12654)
open BstLean.Part268 (cell12654)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085625570653
  | 2 => 0.086570832552
  | 3 => 0.087514604908
  | 4 => 0.088458390899
  | 5 => 0.089404005837
  | 6 => 0.090353623157
  | 7 => 0.091309824661
  | 8 => 0.092275655056
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12654 12654 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12654 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12654

/-! Actual upper energy certificates on all 43 source endpoints at 12654. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12654)
open BstLean.Part268 (cell12654)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12654 (gMinus 12654) (1 - (cell12654 i).lower) ≤ 1 ∧
    energyUpper 12654 (gMinus 12654) (BstLean.Part211.gPlus 12654)
      (finiteEnergy 12654 12654 0.011) (1 - (cell12654 i).lower) ≤
      (cell12654 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨10,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨11,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨12,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨13,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨14,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨15,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨16,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨17,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨18,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨19,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨20,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨21,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨22,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨23,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨24,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨25,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨26,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨27,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨28,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨29,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨30,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨31,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨32,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨33,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨34,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨35,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨36,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨37,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨38,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨39,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨40,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨41,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨42,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨43,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨44,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨45,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨46,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨47,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨48,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨49,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨50,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨51,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12654) (by norm_num)
        (q := 1 - (cell12654 ⟨52,by decide⟩).lower)
        (by norm_num [cell12654]) (by norm_num [cell12654])
      exact ⟨E.1,E.2.trans (by norm_num [cell12654])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12654

/-! Source-cell containment and simple scalar guards at 12654. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12654)
open BstLean.Part268 (cell12654)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12654 ⟨10,by decide⟩).lower ∧ (cell12654 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12654 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12654 ⟨11,by decide⟩).lower ∧ (cell12654 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12654 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12654 ⟨12,by decide⟩).lower ∧ (cell12654 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12654 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12654 ⟨13,by decide⟩).lower ∧ (cell12654 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12654 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12654 ⟨14,by decide⟩).lower ∧ (cell12654 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12654 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12654 ⟨15,by decide⟩).lower ∧ (cell12654 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12654 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12654 ⟨16,by decide⟩).lower ∧ (cell12654 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12654 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12654 ⟨17,by decide⟩).lower ∧ (cell12654 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12654 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12654 ⟨18,by decide⟩).lower ∧ (cell12654 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12654 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12654 ⟨19,by decide⟩).lower ∧ (cell12654 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12654 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12654 ⟨20,by decide⟩).lower ∧ (cell12654 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12654 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12654 ⟨21,by decide⟩).lower ∧ (cell12654 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12654 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12654 ⟨22,by decide⟩).lower ∧ (cell12654 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12654 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12654 ⟨23,by decide⟩).lower ∧ (cell12654 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12654 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12654 ⟨24,by decide⟩).lower ∧ (cell12654 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12654 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12654 ⟨25,by decide⟩).lower ∧ (cell12654 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12654 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12654 ⟨26,by decide⟩).lower ∧ (cell12654 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12654 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12654 ⟨27,by decide⟩).lower ∧ (cell12654 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12654 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12654 ⟨28,by decide⟩).lower ∧ (cell12654 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12654 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12654 ⟨29,by decide⟩).lower ∧ (cell12654 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12654 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12654 ⟨30,by decide⟩).lower ∧ (cell12654 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12654 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12654 ⟨31,by decide⟩).lower ∧ (cell12654 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12654 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12654 ⟨32,by decide⟩).lower ∧ (cell12654 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12654 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12654 ⟨33,by decide⟩).lower ∧ (cell12654 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12654 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12654 ⟨34,by decide⟩).lower ∧ (cell12654 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12654 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12654 ⟨35,by decide⟩).lower ∧ (cell12654 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12654 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12654 ⟨36,by decide⟩).lower ∧ (cell12654 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12654 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12654 ⟨37,by decide⟩).lower ∧ (cell12654 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12654 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12654 ⟨38,by decide⟩).lower ∧ (cell12654 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12654 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12654 ⟨39,by decide⟩).lower ∧ (cell12654 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12654 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12654 ⟨40,by decide⟩).lower ∧ (cell12654 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12654 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12654 ⟨41,by decide⟩).lower ∧ (cell12654 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12654 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12654 ⟨42,by decide⟩).lower ∧ (cell12654 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12654 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12654 ⟨43,by decide⟩).lower ∧ (cell12654 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12654 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12654 ⟨44,by decide⟩).lower ∧ (cell12654 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12654 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12654 ⟨45,by decide⟩).lower ∧ (cell12654 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12654 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12654 ⟨46,by decide⟩).lower ∧ (cell12654 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12654 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12654 ⟨47,by decide⟩).lower ∧ (cell12654 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12654 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12654 ⟨48,by decide⟩).lower ∧ (cell12654 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12654 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12654 ⟨49,by decide⟩).lower ∧ (cell12654 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12654 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12654 ⟨50,by decide⟩).lower ∧ (cell12654 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12654 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12654 ⟨51,by decide⟩).lower ∧ (cell12654 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12654 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12654 ⟨52,by decide⟩).lower ∧ (cell12654 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12654 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12654 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12654 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12654,cell12654,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12654 i).lower ∧
    (cell12654 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12654 i).upper ≤ (0.532 : ℝ) ∧
    (cell12654 i).centre ≤ (0.1 : ℝ) ∧ (cell12654 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12654 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12654 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12654

/-! The local source numeric instances at 12654 have no network premises. -/
namespace BstLean.Part269.N12654
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12654)
open BstLean.Part268 (cell12654)

noncomputable def sourceNumerics12654 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12654 (cell12654 i)
      scalarRow12654.M scalarRow12654.H scalarRow12654.xi := by
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
    energy_allowance := scalarRow12654.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12654]
    centre_nonneg := (scalarRow12654.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12654])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12654
/-! Actual 12655 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12655 ≤ (1.035873392117 : ℝ) := by
  have hr : (112.494444307263 : ℝ) ≤ √(12655 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.494444307263 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12655 12655 (11 / 1000) ≤
    (0.008497193333 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12655) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.494444307263 : ℝ) ≤ √(12655 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12655)
  have hdiv : K / √(12655 : ℝ) ≤ K / 112.494444307263 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.494444307263 ≤ (0.008497193333 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12655.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12655 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12655 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12655 := gPlus_lower 12655
end BstLean.Part269.N12655

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12655
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035873392116 : ℝ) ≤ wn 12655 := by
  have hn : √(12655 : ℝ) ≤ 112.494444307264 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12655 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.494444307264 ≤ 2 / √(12655 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252792194 : ℝ) ≤ rhoBar 12655 BstLean.Part154.csC ∧
    rhoBar 12655 BstLean.Part154.csC ≤ 0.000252792585 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035873392116 : ℝ) / (1.295212 * 12655) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035873392117 : ℝ) / (1.29521 * 12655) := by gcongr
      _ ≤ (0.000252792585 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12655 BstLean.Part154.csC) ≤ 0.001011234245 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12655 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) ≤ 0.000193084714 ∧
    cc1 (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) ≤ 0.000122861079 ∧
    cc2 (rhoBar 12655 BstLean.Part154.csC) ≤ 0.000071321790 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12655 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12655 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12655 BstLean.Part154.csC * nuR (rhoBar 12655 BstLean.Part154.csC)) ≤ 0.000505601146 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252792585 : ℝ) * 0.001011234245 := by gcongr
      _ ≤ (0.000505601146 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12655 BstLean.Part154.csC) * nuR (rhoBar 12655 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011234245 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12655 BstLean.Part154.csC) * rhoBar 12655 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252792585 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252792585 / 2 + 0.399 * 0.001011234245 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193084714 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505601146 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122861079 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252792585 / 1.414213562 := by gcongr
      _ ≤ (0.000071321790 : ℝ) := by norm_num

end BstLean.Part269.N12655

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12655
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) ≤ 1.61002E-7 := by
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12655 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12655 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12655 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193084714 : ℝ) ^ 2 + 0.000122861079 ^ 2 + 3 * 0.000071321790 ^ 2 +
        2 * 0.797885 * 0.000193084714 * 0.000122861079 + 2 * 0.000193084714 * 0.000071321790 +
        4 * 0.797885 * 0.000122861079 * 0.000071321790 := by gcongr
    _ ≤ (1.61002E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12655 BstLean.Part154.csC Θ ≤ 0.002638968953 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12655 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12655 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12655 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035873392117 * 1.61002E-7 / (0.000252792194 : ℝ) := by gcongr
    _ ≤ 0.002638968953 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12655 BstLean.Part154.csC Θ ≤ 0.002928256625 + 0.000666823987 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12655 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12655 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035873392117 : ℝ) * ((2 * Θ * 0.000252792585 +
        (6863 / 10000) * 0.000252792585 * 12655 * 0.001011234245) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002928256625 + 0.000666823987 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12655 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12655 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12655 0.011 Θ ∧ gammaRatio 12655 0.011 Θ ≤ 0.000086903554 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12655 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035873392117 : ℝ) * 0.525 / ((1 - 0.011) * 12655) := by gcongr
      _ ≤ (0.000086903554 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12655 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12655 0.011 Θ) :=
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
    badAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12655 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12655 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12655 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12655 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12655 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12655 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12655 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12655 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12655 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12655 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035873392117 : ℝ) * 12655 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003542568016 + 0.003305792940 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12655

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12655
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12655 BstLean.Part154.csC) (piBar (rhoBar 12655 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12655 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12655 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12655 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12655 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12655 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12655 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12655 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12655 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12655 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12655 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052578557404 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12655) ≤ 0.010615969424 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12655 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035873392117)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010615969424 + 2 * 0.737676 / 12655) := by gcongr
    _ ≤ (0.052578557404 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12655 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12655

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12655
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501526021 : ℝ) ≤ plow 12655 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12655) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784709310)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385458701) : eMP 12655 0.011 xi bn ≤ 0.001192680476 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12655 : ℝ) * (1 - 0.011))) ≤ 0.000589715486 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385458701 / (12655 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589715486 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589715486 : ℝ) + 3.141593 * 0.052784709310 / (12655 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192680476 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784709310)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385458701) : PiBarMP 12655 12 0.011 xi bn ≤ 0.161540149516 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12655 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037221750376 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.874013962135 : ℝ) ≤ √((12655 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.494444307263 : ℝ) ≤ √(12655 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12655) ≤ 0.123849745191 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037221750376 + 0.052784709310 * 1.772454 / (2 * (111.874013962135 : ℝ))) * (1 + 0.001192680476) +
        8 / (12655 * 112.494444307263) + 0.123849745191 := by gcongr
    _ ≤ (0.161540149516 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784709310)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385458701) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282327788763) :
    parallelOracle 12655 0.011 xi bn cd ≤ 0.162533882106 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12655 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12655 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501526021 : ℝ) ≤ plow 12655 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.494444307263 : ℝ) ≤ √(12655 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282327788763 : ℝ) / (2 * 0.560501526021 * 112.494444307263)) * 0.161540149516 +
        0.282327788763 ^ 2 / (2 * 0.560501526021 * 112.494444307263) := by gcongr
    _ ≤ (0.162533882106 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784709310) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385458701)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282327788763) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12655 12655 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501526021 : ℝ) ≤ plow 12655 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.494444307263 : ℝ) ≤ √(12655 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12655 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12655 Θ 1.22 ≤ 0.011788142145 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.494444307263 := by gcongr <;> linarith
      _ ≤ (0.011788142145 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12655 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12655 12655 0.011 ≤ 0.008497193333 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12655 12655 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12655 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12655 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12655 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12655 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162533882106 + 0.011788142145 + (0.008497193333 : ℝ) *
        (1 + 2 * (0.282327788763 + 0.011788142145) / (0.560501526021 * 112.494444307263))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12655]

end BstLean.Part269.N12655

/-! The original eight local profiles supply actual 12655 moment certificates. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12655 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052784709310 ∧
    0 ≤ bN 12655 BstLean.Part154.csC (groupTheta g) ∧ bN 12655 BstLean.Part154.csC (groupTheta g) ≤ 0.001385458701 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12655 12655 0.011
      (momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12655 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12655 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12655 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229749231359 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12655 0.011
      (momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12655 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12655
/-! The actual computed-centre upper energy formula at 12655. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12655

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12655)
open BstLean.Part268 (cell12655)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085622603879
  | 2 => 0.086567810115
  | 3 => 0.087511518501
  | 4 => 0.088455230317
  | 5 => 0.089400758640
  | 6 => 0.090350274298
  | 7 => 0.091306356071
  | 8 => 0.092272045180
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12655 12655 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12655 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12655

/-! Actual upper energy certificates on all 43 source endpoints at 12655. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12655)
open BstLean.Part268 (cell12655)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12655 (gMinus 12655) (1 - (cell12655 i).lower) ≤ 1 ∧
    energyUpper 12655 (gMinus 12655) (BstLean.Part211.gPlus 12655)
      (finiteEnergy 12655 12655 0.011) (1 - (cell12655 i).lower) ≤
      (cell12655 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨10,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨11,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨12,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨13,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨14,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨15,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨16,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨17,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨18,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨19,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨20,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨21,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨22,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨23,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨24,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨25,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨26,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨27,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨28,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨29,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨30,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨31,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨32,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨33,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨34,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨35,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨36,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨37,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨38,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨39,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨40,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨41,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨42,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨43,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨44,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨45,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨46,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨47,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨48,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨49,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨50,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨51,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12655) (by norm_num)
        (q := 1 - (cell12655 ⟨52,by decide⟩).lower)
        (by norm_num [cell12655]) (by norm_num [cell12655])
      exact ⟨E.1,E.2.trans (by norm_num [cell12655])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12655

/-! Source-cell containment and simple scalar guards at 12655. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12655)
open BstLean.Part268 (cell12655)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12655 ⟨10,by decide⟩).lower ∧ (cell12655 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12655 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12655 ⟨11,by decide⟩).lower ∧ (cell12655 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12655 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12655 ⟨12,by decide⟩).lower ∧ (cell12655 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12655 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12655 ⟨13,by decide⟩).lower ∧ (cell12655 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12655 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12655 ⟨14,by decide⟩).lower ∧ (cell12655 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12655 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12655 ⟨15,by decide⟩).lower ∧ (cell12655 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12655 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12655 ⟨16,by decide⟩).lower ∧ (cell12655 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12655 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12655 ⟨17,by decide⟩).lower ∧ (cell12655 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12655 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12655 ⟨18,by decide⟩).lower ∧ (cell12655 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12655 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12655 ⟨19,by decide⟩).lower ∧ (cell12655 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12655 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12655 ⟨20,by decide⟩).lower ∧ (cell12655 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12655 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12655 ⟨21,by decide⟩).lower ∧ (cell12655 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12655 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12655 ⟨22,by decide⟩).lower ∧ (cell12655 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12655 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12655 ⟨23,by decide⟩).lower ∧ (cell12655 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12655 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12655 ⟨24,by decide⟩).lower ∧ (cell12655 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12655 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12655 ⟨25,by decide⟩).lower ∧ (cell12655 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12655 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12655 ⟨26,by decide⟩).lower ∧ (cell12655 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12655 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12655 ⟨27,by decide⟩).lower ∧ (cell12655 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12655 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12655 ⟨28,by decide⟩).lower ∧ (cell12655 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12655 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12655 ⟨29,by decide⟩).lower ∧ (cell12655 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12655 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12655 ⟨30,by decide⟩).lower ∧ (cell12655 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12655 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12655 ⟨31,by decide⟩).lower ∧ (cell12655 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12655 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12655 ⟨32,by decide⟩).lower ∧ (cell12655 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12655 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12655 ⟨33,by decide⟩).lower ∧ (cell12655 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12655 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12655 ⟨34,by decide⟩).lower ∧ (cell12655 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12655 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12655 ⟨35,by decide⟩).lower ∧ (cell12655 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12655 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12655 ⟨36,by decide⟩).lower ∧ (cell12655 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12655 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12655 ⟨37,by decide⟩).lower ∧ (cell12655 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12655 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12655 ⟨38,by decide⟩).lower ∧ (cell12655 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12655 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12655 ⟨39,by decide⟩).lower ∧ (cell12655 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12655 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12655 ⟨40,by decide⟩).lower ∧ (cell12655 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12655 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12655 ⟨41,by decide⟩).lower ∧ (cell12655 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12655 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12655 ⟨42,by decide⟩).lower ∧ (cell12655 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12655 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12655 ⟨43,by decide⟩).lower ∧ (cell12655 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12655 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12655 ⟨44,by decide⟩).lower ∧ (cell12655 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12655 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12655 ⟨45,by decide⟩).lower ∧ (cell12655 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12655 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12655 ⟨46,by decide⟩).lower ∧ (cell12655 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12655 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12655 ⟨47,by decide⟩).lower ∧ (cell12655 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12655 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12655 ⟨48,by decide⟩).lower ∧ (cell12655 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12655 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12655 ⟨49,by decide⟩).lower ∧ (cell12655 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12655 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12655 ⟨50,by decide⟩).lower ∧ (cell12655 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12655 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12655 ⟨51,by decide⟩).lower ∧ (cell12655 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12655 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12655 ⟨52,by decide⟩).lower ∧ (cell12655 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12655 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12655 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12655 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12655,cell12655,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12655 i).lower ∧
    (cell12655 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12655 i).upper ≤ (0.532 : ℝ) ∧
    (cell12655 i).centre ≤ (0.1 : ℝ) ∧ (cell12655 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12655 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12655 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12655

/-! The local source numeric instances at 12655 have no network premises. -/
namespace BstLean.Part269.N12655
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12655)
open BstLean.Part268 (cell12655)

noncomputable def sourceNumerics12655 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12655 (cell12655 i)
      scalarRow12655.M scalarRow12655.H scalarRow12655.xi := by
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
    energy_allowance := scalarRow12655.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12655]
    centre_nonneg := (scalarRow12655.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12655])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12655
/-! Actual 12656 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12656 ≤ (1.035871962353 : ℝ) := by
  have hr : (112.498888883401 : ℝ) ≤ √(12656 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.498888883401 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12656 12656 (11 / 1000) ≤
    (0.008496857626 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12656) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.498888883401 : ℝ) ≤ √(12656 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12656)
  have hdiv : K / √(12656 : ℝ) ≤ K / 112.498888883401 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.498888883401 ≤ (0.008496857626 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12656.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12656 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12656 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12656 := gPlus_lower 12656
end BstLean.Part269.N12656

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12656
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035871962352 : ℝ) ≤ wn 12656 := by
  have hn : √(12656 : ℝ) ≤ 112.498888883402 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12656 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.498888883402 ≤ 2 / √(12656 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252771871 : ℝ) ≤ rhoBar 12656 BstLean.Part154.csC ∧
    rhoBar 12656 BstLean.Part154.csC ≤ 0.000252772262 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035871962352 : ℝ) / (1.295212 * 12656) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035871962353 : ℝ) / (1.29521 * 12656) := by gcongr
      _ ≤ (0.000252772262 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12656 BstLean.Part154.csC) ≤ 0.001011152942 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12656 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) ≤ 0.000193069191 ∧
    cc1 (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) ≤ 0.000122851202 ∧
    cc2 (rhoBar 12656 BstLean.Part154.csC) ≤ 0.000071316056 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12656 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12656 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12656 BstLean.Part154.csC * nuR (rhoBar 12656 BstLean.Part154.csC)) ≤ 0.000505560498 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252772262 : ℝ) * 0.001011152942 := by gcongr
      _ ≤ (0.000505560498 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12656 BstLean.Part154.csC) * nuR (rhoBar 12656 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011152942 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12656 BstLean.Part154.csC) * rhoBar 12656 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252772262 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252772262 / 2 + 0.399 * 0.001011152942 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193069191 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505560498 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122851202 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252772262 / 1.414213562 := by gcongr
      _ ≤ (0.000071316056 : ℝ) := by norm_num

end BstLean.Part269.N12656

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12656
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) ≤ 1.60976E-7 := by
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12656 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12656 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12656 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193069191 : ℝ) ^ 2 + 0.000122851202 ^ 2 + 3 * 0.000071316056 ^ 2 +
        2 * 0.797885 * 0.000193069191 * 0.000122851202 + 2 * 0.000193069191 * 0.000071316056 +
        4 * 0.797885 * 0.000122851202 * 0.000071316056 := by gcongr
    _ ≤ (1.60976E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12656 BstLean.Part154.csC Θ ≤ 0.002638751288 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12656 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12656 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12656 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035871962353 * 1.60976E-7 / (0.000252771871 : ℝ) := by gcongr
    _ ≤ 0.002638751288 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12656 BstLean.Part154.csC Θ ≤ 0.002928013111 + 0.000666769458 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12656 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12656 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035871962353 : ℝ) * ((2 * Θ * 0.000252772262 +
        (6863 / 10000) * 0.000252772262 * 12656 * 0.001011152942) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002928013111 + 0.000666769458 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12656 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12656 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12656 0.011 Θ ∧ gammaRatio 12656 0.011 Θ ≤ 0.000086896568 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12656 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035871962353 : ℝ) * 0.525 / ((1 - 0.011) * 12656) := by gcongr
      _ ≤ (0.000086896568 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12656 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12656 0.011 Θ) :=
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
    badAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12656 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12656 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12656 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12656 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12656 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12656 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12656 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12656 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12656 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12656 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035871962353 : ℝ) * 12656 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003542324502 + 0.003305520746 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12656

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12656
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12656 BstLean.Part154.csC) (piBar (rhoBar 12656 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12656 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12656 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12656 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12656 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12656 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12656 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12656 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12656 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12656 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12656 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052576457581 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12656) ≤ 0.010615550011 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12656 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035871962353)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010615550011 + 2 * 0.737676 / 12656) := by gcongr
    _ ≤ (0.052576457581 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12656 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12656

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12656
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501571562 : ℝ) ≤ plow 12656 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12656) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784322894)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385344427) : eMP 12656 0.011 xi bn ≤ 0.001192584096 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12656 : ℝ) * (1 - 0.011))) ≤ 0.000589667868 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385344427 / (12656 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589667868 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589667868 : ℝ) + 3.141593 * 0.052784322894 / (12656 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192584096 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784322894)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385344427) : PiBarMP 12656 12 0.011 xi bn ≤ 0.161533695689 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12656 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037220215301 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.878434025508 : ℝ) ≤ √((12656 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.498888883401 : ℝ) ≤ √(12656 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12656) ≤ 0.123844852168 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037220215301 + 0.052784322894 * 1.772454 / (2 * (111.878434025508 : ℝ))) * (1 + 0.001192584096) +
        8 / (12656 * 112.498888883401) + 0.123844852168 := by gcongr
    _ ≤ (0.161533695689 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784322894)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385344427) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282324847987) :
    parallelOracle 12656 0.011 xi bn cd ≤ 0.162527357556 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12656 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12656 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501571562 : ℝ) ≤ plow 12656 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.498888883401 : ℝ) ≤ √(12656 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282324847987 : ℝ) / (2 * 0.560501571562 * 112.498888883401)) * 0.161533695689 +
        0.282324847987 ^ 2 / (2 * 0.560501571562 * 112.498888883401) := by gcongr
    _ ≤ (0.162527357556 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052784322894) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385344427)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282324847987) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12656 12656 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501571562 : ℝ) ≤ plow 12656 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.498888883401 : ℝ) ≤ √(12656 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12656 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12656 Θ 1.22 ≤ 0.011787676423 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.498888883401 := by gcongr <;> linarith
      _ ≤ (0.011787676423 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12656 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12656 12656 0.011 ≤ 0.008496857626 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12656 12656 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12656 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12656 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12656 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12656 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162527357556 + 0.011787676423 + (0.008496857626 : ℝ) *
        (1 + 2 * (0.282324847987 + 0.011787676423) / (0.560501571562 * 112.498888883401))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12656]

end BstLean.Part269.N12656

/-! The original eight local profiles supply actual 12656 moment certificates. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12656 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052784322894 ∧
    0 ≤ bN 12656 BstLean.Part154.csC (groupTheta g) ∧ bN 12656 BstLean.Part154.csC (groupTheta g) ≤ 0.001385344427 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12656 12656 0.011
      (momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12656 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12656 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12656 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229748390406 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12656 0.011
      (momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12656 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12656
/-! The actual computed-centre upper energy formula at 12656. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12656

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12656)
open BstLean.Part268 (cell12656)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085619638241
  | 2 => 0.086564788860
  | 3 => 0.087508433335
  | 4 => 0.088452071046
  | 5 => 0.089397512841
  | 6 => 0.090346926945
  | 7 => 0.091302889116
  | 8 => 0.092268437092
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12656 12656 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12656 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12656

/-! Actual upper energy certificates on all 43 source endpoints at 12656. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12656)
open BstLean.Part268 (cell12656)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12656 (gMinus 12656) (1 - (cell12656 i).lower) ≤ 1 ∧
    energyUpper 12656 (gMinus 12656) (BstLean.Part211.gPlus 12656)
      (finiteEnergy 12656 12656 0.011) (1 - (cell12656 i).lower) ≤
      (cell12656 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨10,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨11,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨12,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨13,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨14,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨15,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨16,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨17,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨18,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨19,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨20,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨21,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨22,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨23,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨24,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨25,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨26,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨27,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨28,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨29,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨30,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨31,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨32,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨33,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨34,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨35,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨36,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨37,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨38,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨39,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨40,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨41,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨42,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨43,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨44,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨45,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨46,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨47,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨48,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨49,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨50,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨51,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12656) (by norm_num)
        (q := 1 - (cell12656 ⟨52,by decide⟩).lower)
        (by norm_num [cell12656]) (by norm_num [cell12656])
      exact ⟨E.1,E.2.trans (by norm_num [cell12656])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12656

/-! Source-cell containment and simple scalar guards at 12656. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12656)
open BstLean.Part268 (cell12656)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12656 ⟨10,by decide⟩).lower ∧ (cell12656 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12656 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12656 ⟨11,by decide⟩).lower ∧ (cell12656 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12656 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12656 ⟨12,by decide⟩).lower ∧ (cell12656 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12656 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12656 ⟨13,by decide⟩).lower ∧ (cell12656 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12656 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12656 ⟨14,by decide⟩).lower ∧ (cell12656 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12656 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12656 ⟨15,by decide⟩).lower ∧ (cell12656 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12656 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12656 ⟨16,by decide⟩).lower ∧ (cell12656 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12656 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12656 ⟨17,by decide⟩).lower ∧ (cell12656 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12656 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12656 ⟨18,by decide⟩).lower ∧ (cell12656 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12656 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12656 ⟨19,by decide⟩).lower ∧ (cell12656 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12656 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12656 ⟨20,by decide⟩).lower ∧ (cell12656 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12656 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12656 ⟨21,by decide⟩).lower ∧ (cell12656 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12656 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12656 ⟨22,by decide⟩).lower ∧ (cell12656 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12656 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12656 ⟨23,by decide⟩).lower ∧ (cell12656 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12656 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12656 ⟨24,by decide⟩).lower ∧ (cell12656 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12656 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12656 ⟨25,by decide⟩).lower ∧ (cell12656 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12656 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12656 ⟨26,by decide⟩).lower ∧ (cell12656 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12656 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12656 ⟨27,by decide⟩).lower ∧ (cell12656 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12656 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12656 ⟨28,by decide⟩).lower ∧ (cell12656 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12656 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12656 ⟨29,by decide⟩).lower ∧ (cell12656 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12656 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12656 ⟨30,by decide⟩).lower ∧ (cell12656 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12656 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12656 ⟨31,by decide⟩).lower ∧ (cell12656 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12656 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12656 ⟨32,by decide⟩).lower ∧ (cell12656 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12656 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12656 ⟨33,by decide⟩).lower ∧ (cell12656 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12656 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12656 ⟨34,by decide⟩).lower ∧ (cell12656 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12656 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12656 ⟨35,by decide⟩).lower ∧ (cell12656 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12656 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12656 ⟨36,by decide⟩).lower ∧ (cell12656 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12656 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12656 ⟨37,by decide⟩).lower ∧ (cell12656 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12656 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12656 ⟨38,by decide⟩).lower ∧ (cell12656 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12656 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12656 ⟨39,by decide⟩).lower ∧ (cell12656 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12656 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12656 ⟨40,by decide⟩).lower ∧ (cell12656 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12656 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12656 ⟨41,by decide⟩).lower ∧ (cell12656 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12656 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12656 ⟨42,by decide⟩).lower ∧ (cell12656 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12656 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12656 ⟨43,by decide⟩).lower ∧ (cell12656 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12656 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12656 ⟨44,by decide⟩).lower ∧ (cell12656 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12656 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12656 ⟨45,by decide⟩).lower ∧ (cell12656 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12656 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12656 ⟨46,by decide⟩).lower ∧ (cell12656 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12656 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12656 ⟨47,by decide⟩).lower ∧ (cell12656 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12656 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12656 ⟨48,by decide⟩).lower ∧ (cell12656 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12656 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12656 ⟨49,by decide⟩).lower ∧ (cell12656 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12656 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12656 ⟨50,by decide⟩).lower ∧ (cell12656 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12656 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12656 ⟨51,by decide⟩).lower ∧ (cell12656 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12656 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12656 ⟨52,by decide⟩).lower ∧ (cell12656 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12656 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12656 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12656 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12656,cell12656,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12656 i).lower ∧
    (cell12656 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12656 i).upper ≤ (0.532 : ℝ) ∧
    (cell12656 i).centre ≤ (0.1 : ℝ) ∧ (cell12656 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12656 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12656 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12656

/-! The local source numeric instances at 12656 have no network premises. -/
namespace BstLean.Part269.N12656
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12656)
open BstLean.Part268 (cell12656)

noncomputable def sourceNumerics12656 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12656 (cell12656 i)
      scalarRow12656.M scalarRow12656.H scalarRow12656.xi := by
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
    energy_allowance := scalarRow12656.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12656]
    centre_nonneg := (scalarRow12656.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12656])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12656
/-! Actual 12657 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12657 ≤ (1.035870532760 : ℝ) := by
  have hr : (112.503333283952 : ℝ) ≤ √(12657 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.503333283952 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12657 12657 (11 / 1000) ≤
    (0.008496521958 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12657) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.503333283952 : ℝ) ≤ √(12657 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12657)
  have hdiv : K / √(12657 : ℝ) ≤ K / 112.503333283952 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.503333283952 ≤ (0.008496521958 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12657.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12657 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12657 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12657 := gPlus_lower 12657
end BstLean.Part269.N12657

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12657
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035870532759 : ℝ) ≤ wn 12657 := by
  have hn : √(12657 : ℝ) ≤ 112.503333283953 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12657 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.503333283953 ≤ 2 / √(12657 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252751551 : ℝ) ≤ rhoBar 12657 BstLean.Part154.csC ∧
    rhoBar 12657 BstLean.Part154.csC ≤ 0.000252751943 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035870532759 : ℝ) / (1.295212 * 12657) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035870532760 : ℝ) / (1.29521 * 12657) := by gcongr
      _ ≤ (0.000252751943 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12657 BstLean.Part154.csC) ≤ 0.001011071656 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12657 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) ≤ 0.000193053670 ∧
    cc1 (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) ≤ 0.000122841326 ∧
    cc2 (rhoBar 12657 BstLean.Part154.csC) ≤ 0.000071310323 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12657 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12657 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12657 BstLean.Part154.csC * nuR (rhoBar 12657 BstLean.Part154.csC)) ≤ 0.000505519857 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252751943 : ℝ) * 0.001011071656 := by gcongr
      _ ≤ (0.000505519857 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12657 BstLean.Part154.csC) * nuR (rhoBar 12657 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001011071656 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12657 BstLean.Part154.csC) * rhoBar 12657 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252751943 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252751943 / 2 + 0.399 * 0.001011071656 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193053670 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505519857 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122841326 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252751943 / 1.414213562 := by gcongr
      _ ≤ (0.000071310323 : ℝ) := by norm_num

end BstLean.Part269.N12657

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12657
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) ≤ 1.60950E-7 := by
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12657 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12657 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12657 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193053670 : ℝ) ^ 2 + 0.000122841326 ^ 2 + 3 * 0.000071310323 ^ 2 +
        2 * 0.797885 * 0.000193053670 * 0.000122841326 + 2 * 0.000193053670 * 0.000071310323 +
        4 * 0.797885 * 0.000122841326 * 0.000071310323 := by gcongr
    _ ≤ (1.60950E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12657 BstLean.Part154.csC Θ ≤ 0.002638533558 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12657 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12657 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12657 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035870532760 * 1.60950E-7 / (0.000252751551 : ℝ) := by gcongr
    _ ≤ 0.002638533558 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12657 BstLean.Part154.csC Θ ≤ 0.002927769657 + 0.000666714940 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12657 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12657 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035870532760 : ℝ) * ((2 * Θ * 0.000252751943 +
        (6863 / 10000) * 0.000252751943 * 12657 * 0.001011071656) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002927769657 + 0.000666714940 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12657 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12657 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12657 0.011 Θ ∧ gammaRatio 12657 0.011 Θ ≤ 0.000086889582 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12657 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035870532760 : ℝ) * 0.525 / ((1 - 0.011) * 12657) := by gcongr
      _ ≤ (0.000086889582 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12657 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12657 0.011 Θ) :=
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
    badAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12657 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12657 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12657 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12657 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12657 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12657 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12657 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12657 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12657 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12657 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035870532760 : ℝ) * 12657 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003542081048 + 0.003305248498 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12657

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12657
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12657 BstLean.Part154.csC) (piBar (rhoBar 12657 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12657 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12657 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12657 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12657 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12657 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12657 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12657 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12657 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12657 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12657 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052574358009 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12657) ≤ 0.010615130648 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12657 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035870532760)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010615130648 + 2 * 0.737676 / 12657) := by gcongr
    _ ≤ (0.052574358009 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12657 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12657

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12657
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501617097 : ℝ) ≤ plow 12657 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12657) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783936510)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385230118) : eMP 12657 0.011 xi bn ≤ 0.001192487709 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12657 : ℝ) * (1 - 0.011))) ≤ 0.000589620246 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385230118 / (12657 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589620246 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589620246 : ℝ) + 3.141593 * 0.052783936510 / (12657 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192487709 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783936510)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385230118) : PiBarMP 12657 12 0.011 xi bn ≤ 0.161527241910 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12657 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037218679692 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.882853914261 : ℝ) ≤ √((12657 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.503333283952 : ℝ) ≤ √(12657 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12657) ≤ 0.123839959725 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037218679692 + 0.052783936510 * 1.772454 / (2 * (111.882853914261 : ℝ))) * (1 + 0.001192487709) +
        8 / (12657 * 112.503333283952) + 0.123839959725 := by gcongr
    _ ≤ (0.161527241910 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783936510)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385230118) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282321907529) :
    parallelOracle 12657 0.011 xi bn cd ≤ 0.162520833064 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12657 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12657 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501617097 : ℝ) ≤ plow 12657 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.503333283952 : ℝ) ≤ √(12657 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282321907529 : ℝ) / (2 * 0.560501617097 * 112.503333283952)) * 0.161527241910 +
        0.282321907529 ^ 2 / (2 * 0.560501617097 * 112.503333283952) := by gcongr
    _ ≤ (0.162520833064 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783936510) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385230118)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282321907529) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12657 12657 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501617097 : ℝ) ≤ plow 12657 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.503333283952 : ℝ) ≤ √(12657 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12657 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12657 Θ 1.22 ≤ 0.011787210755 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.503333283952 := by gcongr <;> linarith
      _ ≤ (0.011787210755 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12657 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12657 12657 0.011 ≤ 0.008496521958 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12657 12657 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12657 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12657 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12657 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12657 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162520833064 + 0.011787210755 + (0.008496521958 : ℝ) *
        (1 + 2 * (0.282321907529 + 0.011787210755) / (0.560501617097 * 112.503333283952))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12657]

end BstLean.Part269.N12657

/-! The original eight local profiles supply actual 12657 moment certificates. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12657 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052783936510 ∧
    0 ≤ bN 12657 BstLean.Part154.csC (groupTheta g) ∧ bN 12657 BstLean.Part154.csC (groupTheta g) ≤ 0.001385230118 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12657 12657 0.011
      (momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12657 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12657 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12657 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229747549520 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12657 0.011
      (momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12657 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12657
/-! The actual computed-centre upper energy formula at 12657. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12657

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12657)
open BstLean.Part268 (cell12657)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085616673737
  | 2 => 0.086561768786
  | 3 => 0.087505349407
  | 4 => 0.088448913085
  | 5 => 0.089394268441
  | 6 => 0.090343581096
  | 7 => 0.091299423793
  | 8 => 0.092264830790
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12657 12657 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12657 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12657

/-! Actual upper energy certificates on all 43 source endpoints at 12657. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12657)
open BstLean.Part268 (cell12657)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12657 (gMinus 12657) (1 - (cell12657 i).lower) ≤ 1 ∧
    energyUpper 12657 (gMinus 12657) (BstLean.Part211.gPlus 12657)
      (finiteEnergy 12657 12657 0.011) (1 - (cell12657 i).lower) ≤
      (cell12657 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨10,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨11,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨12,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨13,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨14,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨15,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨16,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨17,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨18,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨19,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨20,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨21,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨22,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨23,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨24,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨25,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨26,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨27,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨28,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨29,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨30,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨31,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨32,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨33,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨34,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨35,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨36,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨37,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨38,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨39,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨40,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨41,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨42,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨43,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨44,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨45,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨46,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨47,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨48,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨49,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨50,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨51,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12657) (by norm_num)
        (q := 1 - (cell12657 ⟨52,by decide⟩).lower)
        (by norm_num [cell12657]) (by norm_num [cell12657])
      exact ⟨E.1,E.2.trans (by norm_num [cell12657])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12657

/-! Source-cell containment and simple scalar guards at 12657. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12657)
open BstLean.Part268 (cell12657)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12657 ⟨10,by decide⟩).lower ∧ (cell12657 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12657 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12657 ⟨11,by decide⟩).lower ∧ (cell12657 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12657 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12657 ⟨12,by decide⟩).lower ∧ (cell12657 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12657 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12657 ⟨13,by decide⟩).lower ∧ (cell12657 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12657 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12657 ⟨14,by decide⟩).lower ∧ (cell12657 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12657 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12657 ⟨15,by decide⟩).lower ∧ (cell12657 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12657 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12657 ⟨16,by decide⟩).lower ∧ (cell12657 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12657 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12657 ⟨17,by decide⟩).lower ∧ (cell12657 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12657 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12657 ⟨18,by decide⟩).lower ∧ (cell12657 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12657 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12657 ⟨19,by decide⟩).lower ∧ (cell12657 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12657 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12657 ⟨20,by decide⟩).lower ∧ (cell12657 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12657 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12657 ⟨21,by decide⟩).lower ∧ (cell12657 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12657 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12657 ⟨22,by decide⟩).lower ∧ (cell12657 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12657 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12657 ⟨23,by decide⟩).lower ∧ (cell12657 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12657 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12657 ⟨24,by decide⟩).lower ∧ (cell12657 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12657 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12657 ⟨25,by decide⟩).lower ∧ (cell12657 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12657 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12657 ⟨26,by decide⟩).lower ∧ (cell12657 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12657 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12657 ⟨27,by decide⟩).lower ∧ (cell12657 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12657 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12657 ⟨28,by decide⟩).lower ∧ (cell12657 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12657 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12657 ⟨29,by decide⟩).lower ∧ (cell12657 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12657 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12657 ⟨30,by decide⟩).lower ∧ (cell12657 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12657 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12657 ⟨31,by decide⟩).lower ∧ (cell12657 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12657 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12657 ⟨32,by decide⟩).lower ∧ (cell12657 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12657 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12657 ⟨33,by decide⟩).lower ∧ (cell12657 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12657 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12657 ⟨34,by decide⟩).lower ∧ (cell12657 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12657 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12657 ⟨35,by decide⟩).lower ∧ (cell12657 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12657 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12657 ⟨36,by decide⟩).lower ∧ (cell12657 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12657 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12657 ⟨37,by decide⟩).lower ∧ (cell12657 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12657 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12657 ⟨38,by decide⟩).lower ∧ (cell12657 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12657 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12657 ⟨39,by decide⟩).lower ∧ (cell12657 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12657 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12657 ⟨40,by decide⟩).lower ∧ (cell12657 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12657 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12657 ⟨41,by decide⟩).lower ∧ (cell12657 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12657 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12657 ⟨42,by decide⟩).lower ∧ (cell12657 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12657 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12657 ⟨43,by decide⟩).lower ∧ (cell12657 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12657 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12657 ⟨44,by decide⟩).lower ∧ (cell12657 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12657 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12657 ⟨45,by decide⟩).lower ∧ (cell12657 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12657 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12657 ⟨46,by decide⟩).lower ∧ (cell12657 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12657 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12657 ⟨47,by decide⟩).lower ∧ (cell12657 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12657 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12657 ⟨48,by decide⟩).lower ∧ (cell12657 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12657 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12657 ⟨49,by decide⟩).lower ∧ (cell12657 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12657 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12657 ⟨50,by decide⟩).lower ∧ (cell12657 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12657 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12657 ⟨51,by decide⟩).lower ∧ (cell12657 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12657 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12657 ⟨52,by decide⟩).lower ∧ (cell12657 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12657 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12657 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12657 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12657,cell12657,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12657 i).lower ∧
    (cell12657 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12657 i).upper ≤ (0.532 : ℝ) ∧
    (cell12657 i).centre ≤ (0.1 : ℝ) ∧ (cell12657 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12657 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12657 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12657

/-! The local source numeric instances at 12657 have no network premises. -/
namespace BstLean.Part269.N12657
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12657)
open BstLean.Part268 (cell12657)

noncomputable def sourceNumerics12657 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12657 (cell12657 i)
      scalarRow12657.M scalarRow12657.H scalarRow12657.xi := by
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
    energy_allowance := scalarRow12657.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12657]
    centre_nonneg := (scalarRow12657.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12657])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12657
/-! Actual 12658 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12658 ≤ (1.035869103337 : ℝ) := by
  have hr : (112.507777508934 : ℝ) ≤ √(12658 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.507777508934 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12658 12658 (11 / 1000) ≤
    (0.008496186330 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12658) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.507777508934 : ℝ) ≤ √(12658 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12658)
  have hdiv : K / √(12658 : ℝ) ≤ K / 112.507777508934 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.507777508934 ≤ (0.008496186330 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12658.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12658 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12658 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12658 := gPlus_lower 12658
end BstLean.Part269.N12658

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12658
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035869103336 : ℝ) ≤ wn 12658 := by
  have hn : √(12658 : ℝ) ≤ 112.507777508935 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12658 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.507777508935 ≤ 2 / √(12658 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252731235 : ℝ) ≤ rhoBar 12658 BstLean.Part154.csC ∧
    rhoBar 12658 BstLean.Part154.csC ≤ 0.000252731626 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035869103336 : ℝ) / (1.295212 * 12658) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035869103337 : ℝ) / (1.29521 * 12658) := by gcongr
      _ ≤ (0.000252731626 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12658 BstLean.Part154.csC) ≤ 0.001010990378 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12658 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) ≤ 0.000193038151 ∧
    cc1 (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) ≤ 0.000122831451 ∧
    cc2 (rhoBar 12658 BstLean.Part154.csC) ≤ 0.000071304591 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12658 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12658 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12658 BstLean.Part154.csC * nuR (rhoBar 12658 BstLean.Part154.csC)) ≤ 0.000505479221 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252731626 : ℝ) * 0.001010990378 := by gcongr
      _ ≤ (0.000505479221 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12658 BstLean.Part154.csC) * nuR (rhoBar 12658 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010990378 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12658 BstLean.Part154.csC) * rhoBar 12658 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252731626 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252731626 / 2 + 0.399 * 0.001010990378 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193038151 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505479221 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122831451 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252731626 / 1.414213562 := by gcongr
      _ ≤ (0.000071304591 : ℝ) := by norm_num

end BstLean.Part269.N12658

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12658
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) ≤ 1.60924E-7 := by
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12658 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12658 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12658 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193038151 : ℝ) ^ 2 + 0.000122831451 ^ 2 + 3 * 0.000071304591 ^ 2 +
        2 * 0.797885 * 0.000193038151 * 0.000122831451 + 2 * 0.000193038151 * 0.000071304591 +
        4 * 0.797885 * 0.000122831451 * 0.000071304591 := by gcongr
    _ ≤ (1.60924E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12658 BstLean.Part154.csC Θ ≤ 0.002638315753 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12658 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12658 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12658 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035869103337 * 1.60924E-7 / (0.000252731235 : ℝ) := by gcongr
    _ ≤ 0.002638315753 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12658 BstLean.Part154.csC Θ ≤ 0.002927526215 + 0.000666660427 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12658 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12658 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035869103337 : ℝ) * ((2 * Θ * 0.000252731626 +
        (6863 / 10000) * 0.000252731626 * 12658 * 0.001010990378) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002927526215 + 0.000666660427 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12658 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12658 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12658 0.011 Θ ∧ gammaRatio 12658 0.011 Θ ≤ 0.000086882598 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12658 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035869103337 : ℝ) * 0.525 / ((1 - 0.011) * 12658) := by gcongr
      _ ≤ (0.000086882598 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12658 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12658 0.011 Θ) :=
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
    badAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12658 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12658 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12658 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12658 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12658 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12658 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12658 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12658 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12658 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12658 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035869103337 : ℝ) * 12658 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003541837606 + 0.003304976180 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12658

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12658
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12658 BstLean.Part154.csC) (piBar (rhoBar 12658 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12658 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12658 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12658 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12658 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12658 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12658 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12658 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12658 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12658 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12658 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052572258685 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12658) ≤ 0.010614711334 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12658 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035869103337)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010614711334 + 2 * 0.737676 / 12658) := by gcongr
    _ ≤ (0.052572258685 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12658 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12658

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12658
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501662624 : ℝ) ≤ plow 12658 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12658) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783550101)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385115771) : eMP 12658 0.011 xi bn ≤ 0.001192391313 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12658 : ℝ) * (1 - 0.011))) ≤ 0.000589572620 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385115771 / (12658 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589572620 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589572620 : ℝ) + 3.141593 * 0.052783550101 / (12658 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192391313 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783550101)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385115771) : PiBarMP 12658 12 0.011 xi bn ≤ 0.161520788140 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12658 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037217143510 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.887273628415 : ℝ) ≤ √((12658 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.507777508934 : ℝ) ≤ √(12658 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12658) ≤ 0.123835067862 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037217143510 + 0.052783550101 * 1.772454 / (2 * (111.887273628415 : ℝ))) * (1 + 0.001192391313) +
        8 / (12658 * 112.507777508934) + 0.123835067862 := by gcongr
    _ ≤ (0.161520788140 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783550101)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385115771) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282318967260) :
    parallelOracle 12658 0.011 xi bn cd ≤ 0.162514308589 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12658 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12658 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501662624 : ℝ) ≤ plow 12658 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.507777508934 : ℝ) ≤ √(12658 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282318967260 : ℝ) / (2 * 0.560501662624 * 112.507777508934)) * 0.161520788140 +
        0.282318967260 ^ 2 / (2 * 0.560501662624 * 112.507777508934) := by gcongr
    _ ≤ (0.162514308589 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783550101) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385115771)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282318967260) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12658 12658 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501662624 : ℝ) ≤ plow 12658 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.507777508934 : ℝ) ≤ √(12658 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12658 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12658 Θ 1.22 ≤ 0.011786745143 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.507777508934 := by gcongr <;> linarith
      _ ≤ (0.011786745143 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12658 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12658 12658 0.011 ≤ 0.008496186330 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12658 12658 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12658 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12658 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12658 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12658 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162514308589 + 0.011786745143 + (0.008496186330 : ℝ) *
        (1 + 2 * (0.282318967260 + 0.011786745143) / (0.560501662624 * 112.507777508934))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12658]

end BstLean.Part269.N12658

/-! The original eight local profiles supply actual 12658 moment certificates. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12658 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052783550101 ∧
    0 ≤ bN 12658 BstLean.Part154.csC (groupTheta g) ∧ bN 12658 BstLean.Part154.csC (groupTheta g) ≤ 0.001385115771 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12658 12658 0.011
      (momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12658 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12658 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12658 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229746708575 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12658 0.011
      (momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12658 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12658
/-! The actual computed-centre upper energy formula at 12658. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12658

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12658)
open BstLean.Part268 (cell12658)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085613710364
  | 2 => 0.086558749891
  | 3 => 0.087502266717
  | 4 => 0.088445756433
  | 5 => 0.089391025436
  | 6 => 0.090340236750
  | 7 => 0.091295960101
  | 8 => 0.092261226273
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12658 12658 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12658 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12658

/-! Actual upper energy certificates on all 43 source endpoints at 12658. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12658)
open BstLean.Part268 (cell12658)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12658 (gMinus 12658) (1 - (cell12658 i).lower) ≤ 1 ∧
    energyUpper 12658 (gMinus 12658) (BstLean.Part211.gPlus 12658)
      (finiteEnergy 12658 12658 0.011) (1 - (cell12658 i).lower) ≤
      (cell12658 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨10,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨11,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨12,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨13,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨14,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨15,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨16,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨17,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨18,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨19,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨20,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨21,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨22,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨23,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨24,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨25,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨26,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨27,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨28,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨29,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨30,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨31,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨32,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨33,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨34,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨35,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨36,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨37,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨38,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨39,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨40,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨41,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨42,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨43,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨44,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨45,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨46,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨47,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨48,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨49,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨50,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨51,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12658) (by norm_num)
        (q := 1 - (cell12658 ⟨52,by decide⟩).lower)
        (by norm_num [cell12658]) (by norm_num [cell12658])
      exact ⟨E.1,E.2.trans (by norm_num [cell12658])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12658

/-! Source-cell containment and simple scalar guards at 12658. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12658)
open BstLean.Part268 (cell12658)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12658 ⟨10,by decide⟩).lower ∧ (cell12658 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12658 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12658 ⟨11,by decide⟩).lower ∧ (cell12658 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12658 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12658 ⟨12,by decide⟩).lower ∧ (cell12658 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12658 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12658 ⟨13,by decide⟩).lower ∧ (cell12658 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12658 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12658 ⟨14,by decide⟩).lower ∧ (cell12658 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12658 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12658 ⟨15,by decide⟩).lower ∧ (cell12658 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12658 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12658 ⟨16,by decide⟩).lower ∧ (cell12658 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12658 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12658 ⟨17,by decide⟩).lower ∧ (cell12658 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12658 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12658 ⟨18,by decide⟩).lower ∧ (cell12658 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12658 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12658 ⟨19,by decide⟩).lower ∧ (cell12658 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12658 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12658 ⟨20,by decide⟩).lower ∧ (cell12658 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12658 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12658 ⟨21,by decide⟩).lower ∧ (cell12658 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12658 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12658 ⟨22,by decide⟩).lower ∧ (cell12658 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12658 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12658 ⟨23,by decide⟩).lower ∧ (cell12658 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12658 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12658 ⟨24,by decide⟩).lower ∧ (cell12658 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12658 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12658 ⟨25,by decide⟩).lower ∧ (cell12658 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12658 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12658 ⟨26,by decide⟩).lower ∧ (cell12658 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12658 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12658 ⟨27,by decide⟩).lower ∧ (cell12658 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12658 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12658 ⟨28,by decide⟩).lower ∧ (cell12658 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12658 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12658 ⟨29,by decide⟩).lower ∧ (cell12658 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12658 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12658 ⟨30,by decide⟩).lower ∧ (cell12658 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12658 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12658 ⟨31,by decide⟩).lower ∧ (cell12658 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12658 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12658 ⟨32,by decide⟩).lower ∧ (cell12658 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12658 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12658 ⟨33,by decide⟩).lower ∧ (cell12658 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12658 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12658 ⟨34,by decide⟩).lower ∧ (cell12658 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12658 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12658 ⟨35,by decide⟩).lower ∧ (cell12658 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12658 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12658 ⟨36,by decide⟩).lower ∧ (cell12658 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12658 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12658 ⟨37,by decide⟩).lower ∧ (cell12658 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12658 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12658 ⟨38,by decide⟩).lower ∧ (cell12658 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12658 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12658 ⟨39,by decide⟩).lower ∧ (cell12658 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12658 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12658 ⟨40,by decide⟩).lower ∧ (cell12658 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12658 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12658 ⟨41,by decide⟩).lower ∧ (cell12658 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12658 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12658 ⟨42,by decide⟩).lower ∧ (cell12658 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12658 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12658 ⟨43,by decide⟩).lower ∧ (cell12658 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12658 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12658 ⟨44,by decide⟩).lower ∧ (cell12658 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12658 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12658 ⟨45,by decide⟩).lower ∧ (cell12658 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12658 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12658 ⟨46,by decide⟩).lower ∧ (cell12658 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12658 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12658 ⟨47,by decide⟩).lower ∧ (cell12658 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12658 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12658 ⟨48,by decide⟩).lower ∧ (cell12658 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12658 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12658 ⟨49,by decide⟩).lower ∧ (cell12658 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12658 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12658 ⟨50,by decide⟩).lower ∧ (cell12658 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12658 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12658 ⟨51,by decide⟩).lower ∧ (cell12658 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12658 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12658 ⟨52,by decide⟩).lower ∧ (cell12658 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12658 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12658 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12658 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12658,cell12658,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12658 i).lower ∧
    (cell12658 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12658 i).upper ≤ (0.532 : ℝ) ∧
    (cell12658 i).centre ≤ (0.1 : ℝ) ∧ (cell12658 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12658 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12658 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12658

/-! The local source numeric instances at 12658 have no network premises. -/
namespace BstLean.Part269.N12658
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12658)
open BstLean.Part268 (cell12658)

noncomputable def sourceNumerics12658 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12658 (cell12658 i)
      scalarRow12658.M scalarRow12658.H scalarRow12658.xi := by
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
    energy_allowance := scalarRow12658.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12658]
    centre_nonneg := (scalarRow12658.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12658])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12658
/-! Actual 12659 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12659 ≤ (1.035867674085 : ℝ) := by
  have hr : (112.512221558371 : ℝ) ≤ √(12659 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.512221558371 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12659 12659 (11 / 1000) ≤
    (0.008495850742 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12659) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.512221558371 : ℝ) ≤ √(12659 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12659)
  have hdiv : K / √(12659 : ℝ) ≤ K / 112.512221558371 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.512221558371 ≤ (0.008495850742 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12659.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12659 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12659 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12659 := gPlus_lower 12659
end BstLean.Part269.N12659

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12659
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035867674084 : ℝ) ≤ wn 12659 := by
  have hn : √(12659 : ℝ) ≤ 112.512221558372 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12659 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.512221558372 ≤ 2 / √(12659 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252710922 : ℝ) ≤ rhoBar 12659 BstLean.Part154.csC ∧
    rhoBar 12659 BstLean.Part154.csC ≤ 0.000252711313 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035867674084 : ℝ) / (1.295212 * 12659) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035867674085 : ℝ) / (1.29521 * 12659) := by gcongr
      _ ≤ (0.000252711313 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12659 BstLean.Part154.csC) ≤ 0.001010909116 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12659 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) ≤ 0.000193022635 ∧
    cc1 (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) ≤ 0.000122821578 ∧
    cc2 (rhoBar 12659 BstLean.Part154.csC) ≤ 0.000071298860 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12659 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12659 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12659 BstLean.Part154.csC * nuR (rhoBar 12659 BstLean.Part154.csC)) ≤ 0.000505438592 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252711313 : ℝ) * 0.001010909116 := by gcongr
      _ ≤ (0.000505438592 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12659 BstLean.Part154.csC) * nuR (rhoBar 12659 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010909116 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12659 BstLean.Part154.csC) * rhoBar 12659 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252711313 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252711313 / 2 + 0.399 * 0.001010909116 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193022635 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505438592 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122821578 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252711313 / 1.414213562 := by gcongr
      _ ≤ (0.000071298860 : ℝ) := by norm_num

end BstLean.Part269.N12659

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12659
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) ≤ 1.60898E-7 := by
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12659 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12659 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12659 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193022635 : ℝ) ^ 2 + 0.000122821578 ^ 2 + 3 * 0.000071298860 ^ 2 +
        2 * 0.797885 * 0.000193022635 * 0.000122821578 + 2 * 0.000193022635 * 0.000071298860 +
        4 * 0.797885 * 0.000122821578 * 0.000071298860 := by gcongr
    _ ≤ (1.60898E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12659 BstLean.Part154.csC Θ ≤ 0.002638097883 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12659 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12659 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12659 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035867674085 * 1.60898E-7 / (0.000252710922 : ℝ) := by gcongr
    _ ≤ 0.002638097883 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12659 BstLean.Part154.csC Θ ≤ 0.002927282829 + 0.000666605925 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12659 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12659 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035867674085 : ℝ) * ((2 * Θ * 0.000252711313 +
        (6863 / 10000) * 0.000252711313 * 12659 * 0.001010909116) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002927282829 + 0.000666605925 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12659 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12659 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12659 0.011 Θ ∧ gammaRatio 12659 0.011 Θ ≤ 0.000086875615 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12659 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035867674085 : ℝ) * 0.525 / ((1 - 0.011) * 12659) := by gcongr
      _ ≤ (0.000086875615 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12659 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12659 0.011 Θ) :=
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
    badAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12659 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12659 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12659 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12659 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12659 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12659 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12659 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12659 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12659 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12659 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035867674085 : ℝ) * 12659 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003541594220 + 0.003304703808 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12659

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12659
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12659 BstLean.Part154.csC) (piBar (rhoBar 12659 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12659 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12659 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12659 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12659 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12659 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12659 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12659 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12659 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12659 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12659 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052570159613 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12659) ≤ 0.010614292070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12659 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035867674085)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010614292070 + 2 * 0.737676 / 12659) := by gcongr
    _ ≤ (0.052570159613 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12659 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12659

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12659
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501708144 : ℝ) ≤ plow 12659 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12659) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783163720)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385001389) : eMP 12659 0.011 xi bn ≤ 0.001192294910 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12659 : ℝ) * (1 - 0.011))) ≤ 0.000589524990 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001385001389 / (12659 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589524990 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589524990 : ℝ) + 3.141593 * 0.052783163720 / (12659 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192294910 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783163720)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385001389) : PiBarMP 12659 12 0.011 xi bn ≤ 0.161514334417 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12659 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037215606794 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.891693167991 : ℝ) ≤ √((12659 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.512221558371 : ℝ) ≤ √(12659 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12659) ≤ 0.123830176578 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037215606794 + 0.052783163720 * 1.772454 / (2 * (111.891693167991 : ℝ))) * (1 + 0.001192294910) +
        8 / (12659 * 112.512221558371) + 0.123830176578 := by gcongr
    _ ≤ (0.161514334417 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783163720)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385001389) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282316027302) :
    parallelOracle 12659 0.011 xi bn cd ≤ 0.162507784171 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12659 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12659 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501708144 : ℝ) ≤ plow 12659 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.512221558371 : ℝ) ≤ √(12659 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282316027302 : ℝ) / (2 * 0.560501708144 * 112.512221558371)) * 0.161514334417 +
        0.282316027302 ^ 2 / (2 * 0.560501708144 * 112.512221558371) := by gcongr
    _ ≤ (0.162507784171 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052783163720) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001385001389)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282316027302) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12659 12659 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501708144 : ℝ) ≤ plow 12659 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.512221558371 : ℝ) ≤ √(12659 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12659 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12659 Θ 1.22 ≤ 0.011786279585 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.512221558371 := by gcongr <;> linarith
      _ ≤ (0.011786279585 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12659 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12659 12659 0.011 ≤ 0.008495850742 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12659 12659 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12659 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12659 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12659 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12659 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162507784171 + 0.011786279585 + (0.008495850742 : ℝ) *
        (1 + 2 * (0.282316027302 + 0.011786279585) / (0.560501708144 * 112.512221558371))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12659]

end BstLean.Part269.N12659

/-! The original eight local profiles supply actual 12659 moment certificates. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12659 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052783163720 ∧
    0 ≤ bN 12659 BstLean.Part154.csC (groupTheta g) ∧ bN 12659 BstLean.Part154.csC (groupTheta g) ≤ 0.001385001389 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12659 12659 0.011
      (momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12659 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12659 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12659 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229745867689 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12659 0.011
      (momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12659 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12659
/-! The actual computed-centre upper energy formula at 12659. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12659

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12659)
open BstLean.Part268 (cell12659)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085610748124
  | 2 => 0.086555732175
  | 3 => 0.087499185263
  | 4 => 0.088442601089
  | 5 => 0.089387783827
  | 6 => 0.090336893904
  | 7 => 0.091292498037
  | 8 => 0.092257623539
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12659 12659 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12659 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12659

/-! Actual upper energy certificates on all 43 source endpoints at 12659. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12659)
open BstLean.Part268 (cell12659)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12659 (gMinus 12659) (1 - (cell12659 i).lower) ≤ 1 ∧
    energyUpper 12659 (gMinus 12659) (BstLean.Part211.gPlus 12659)
      (finiteEnergy 12659 12659 0.011) (1 - (cell12659 i).lower) ≤
      (cell12659 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨10,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨11,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨12,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨13,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨14,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨15,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨16,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨17,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨18,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨19,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨20,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨21,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨22,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨23,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨24,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨25,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨26,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨27,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨28,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨29,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨30,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨31,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨32,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨33,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨34,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨35,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨36,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨37,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨38,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨39,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨40,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨41,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨42,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨43,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨44,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨45,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨46,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨47,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨48,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨49,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨50,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨51,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12659) (by norm_num)
        (q := 1 - (cell12659 ⟨52,by decide⟩).lower)
        (by norm_num [cell12659]) (by norm_num [cell12659])
      exact ⟨E.1,E.2.trans (by norm_num [cell12659])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12659

/-! Source-cell containment and simple scalar guards at 12659. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12659)
open BstLean.Part268 (cell12659)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12659 ⟨10,by decide⟩).lower ∧ (cell12659 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12659 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12659 ⟨11,by decide⟩).lower ∧ (cell12659 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12659 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12659 ⟨12,by decide⟩).lower ∧ (cell12659 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12659 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12659 ⟨13,by decide⟩).lower ∧ (cell12659 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12659 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12659 ⟨14,by decide⟩).lower ∧ (cell12659 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12659 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12659 ⟨15,by decide⟩).lower ∧ (cell12659 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12659 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12659 ⟨16,by decide⟩).lower ∧ (cell12659 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12659 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12659 ⟨17,by decide⟩).lower ∧ (cell12659 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12659 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12659 ⟨18,by decide⟩).lower ∧ (cell12659 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12659 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12659 ⟨19,by decide⟩).lower ∧ (cell12659 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12659 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12659 ⟨20,by decide⟩).lower ∧ (cell12659 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12659 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12659 ⟨21,by decide⟩).lower ∧ (cell12659 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12659 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12659 ⟨22,by decide⟩).lower ∧ (cell12659 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12659 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12659 ⟨23,by decide⟩).lower ∧ (cell12659 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12659 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12659 ⟨24,by decide⟩).lower ∧ (cell12659 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12659 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12659 ⟨25,by decide⟩).lower ∧ (cell12659 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12659 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12659 ⟨26,by decide⟩).lower ∧ (cell12659 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12659 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12659 ⟨27,by decide⟩).lower ∧ (cell12659 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12659 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12659 ⟨28,by decide⟩).lower ∧ (cell12659 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12659 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12659 ⟨29,by decide⟩).lower ∧ (cell12659 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12659 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12659 ⟨30,by decide⟩).lower ∧ (cell12659 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12659 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12659 ⟨31,by decide⟩).lower ∧ (cell12659 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12659 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12659 ⟨32,by decide⟩).lower ∧ (cell12659 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12659 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12659 ⟨33,by decide⟩).lower ∧ (cell12659 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12659 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12659 ⟨34,by decide⟩).lower ∧ (cell12659 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12659 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12659 ⟨35,by decide⟩).lower ∧ (cell12659 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12659 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12659 ⟨36,by decide⟩).lower ∧ (cell12659 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12659 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12659 ⟨37,by decide⟩).lower ∧ (cell12659 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12659 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12659 ⟨38,by decide⟩).lower ∧ (cell12659 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12659 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12659 ⟨39,by decide⟩).lower ∧ (cell12659 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12659 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12659 ⟨40,by decide⟩).lower ∧ (cell12659 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12659 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12659 ⟨41,by decide⟩).lower ∧ (cell12659 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12659 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12659 ⟨42,by decide⟩).lower ∧ (cell12659 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12659 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12659 ⟨43,by decide⟩).lower ∧ (cell12659 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12659 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12659 ⟨44,by decide⟩).lower ∧ (cell12659 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12659 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12659 ⟨45,by decide⟩).lower ∧ (cell12659 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12659 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12659 ⟨46,by decide⟩).lower ∧ (cell12659 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12659 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12659 ⟨47,by decide⟩).lower ∧ (cell12659 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12659 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12659 ⟨48,by decide⟩).lower ∧ (cell12659 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12659 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12659 ⟨49,by decide⟩).lower ∧ (cell12659 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12659 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12659 ⟨50,by decide⟩).lower ∧ (cell12659 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12659 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12659 ⟨51,by decide⟩).lower ∧ (cell12659 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12659 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12659 ⟨52,by decide⟩).lower ∧ (cell12659 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12659 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12659 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12659 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12659,cell12659,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12659 i).lower ∧
    (cell12659 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12659 i).upper ≤ (0.532 : ℝ) ∧
    (cell12659 i).centre ≤ (0.1 : ℝ) ∧ (cell12659 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12659 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12659 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12659

/-! The local source numeric instances at 12659 have no network premises. -/
namespace BstLean.Part269.N12659
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12659)
open BstLean.Part268 (cell12659)

noncomputable def sourceNumerics12659 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12659 (cell12659 i)
      scalarRow12659.M scalarRow12659.H scalarRow12659.xi := by
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
    energy_allowance := scalarRow12659.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12659]
    centre_nonneg := (scalarRow12659.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12659])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12659
/-! Actual 12660 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12660 ≤ (1.035866245003 : ℝ) := by
  have hr : (112.516665432281 : ℝ) ≤ √(12660 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.516665432281 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12660 12660 (11 / 1000) ≤
    (0.008495515194 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12660) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.516665432281 : ℝ) ≤ √(12660 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12660)
  have hdiv : K / √(12660 : ℝ) ≤ K / 112.516665432281 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.516665432281 ≤ (0.008495515194 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12660.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12660 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12660 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12660 := gPlus_lower 12660
end BstLean.Part269.N12660

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12660
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035866245002 : ℝ) ≤ wn 12660 := by
  have hn : √(12660 : ℝ) ≤ 112.516665432282 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12660 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.516665432282 ≤ 2 / √(12660 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252690612 : ℝ) ≤ rhoBar 12660 BstLean.Part154.csC ∧
    rhoBar 12660 BstLean.Part154.csC ≤ 0.000252691003 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035866245002 : ℝ) / (1.295212 * 12660) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035866245003 : ℝ) / (1.29521 * 12660) := by gcongr
      _ ≤ (0.000252691003 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12660 BstLean.Part154.csC) ≤ 0.001010827865 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12660 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) ≤ 0.000193007122 ∧
    cc1 (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) ≤ 0.000122811707 ∧
    cc2 (rhoBar 12660 BstLean.Part154.csC) ≤ 0.000071293130 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12660 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12660 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12660 BstLean.Part154.csC * nuR (rhoBar 12660 BstLean.Part154.csC)) ≤ 0.000505397969 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252691003 : ℝ) * 0.001010827865 := by gcongr
      _ ≤ (0.000505397969 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12660 BstLean.Part154.csC) * nuR (rhoBar 12660 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010827865 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12660 BstLean.Part154.csC) * rhoBar 12660 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252691003 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252691003 / 2 + 0.399 * 0.001010827865 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193007122 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505397969 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122811707 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252691003 / 1.414213562 := by gcongr
      _ ≤ (0.000071293130 : ℝ) := by norm_num

end BstLean.Part269.N12660

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12660
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) ≤ 1.60873E-7 := by
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12660 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12660 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12660 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193007122 : ℝ) ^ 2 + 0.000122811707 ^ 2 + 3 * 0.000071293130 ^ 2 +
        2 * 0.797885 * 0.000193007122 * 0.000122811707 + 2 * 0.000193007122 * 0.000071293130 +
        4 * 0.797885 * 0.000122811707 * 0.000071293130 := by gcongr
    _ ≤ (1.60873E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12660 BstLean.Part154.csC Θ ≤ 0.002637896345 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12660 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12660 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12660 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035866245003 * 1.60873E-7 / (0.000252690612 : ℝ) := by gcongr
    _ ≤ 0.002637896345 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12660 BstLean.Part154.csC Θ ≤ 0.002927039475 + 0.000666551432 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12660 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12660 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035866245003 : ℝ) * ((2 * Θ * 0.000252691003 +
        (6863 / 10000) * 0.000252691003 * 12660 * 0.001010827865) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002927039475 + 0.000666551432 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12660 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12660 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12660 0.011 Θ ∧ gammaRatio 12660 0.011 Θ ≤ 0.000086868633 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12660 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035866245003 : ℝ) * 0.525 / ((1 - 0.011) * 12660) := by gcongr
      _ ≤ (0.000086868633 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12660 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12660 0.011 Θ) :=
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
    badAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12660 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12660 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12660 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12660 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12660 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12660 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12660 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12660 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12660 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12660 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035866245003 : ℝ) * 12660 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003541350866 + 0.003304447777 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12660

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12660
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12660 BstLean.Part154.csC) (piBar (rhoBar 12660 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12660 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12660 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12660 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12660 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12660 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12660 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12660 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12660 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12660 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12660 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052568060793 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12660) ≤ 0.010613872856 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12660 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035866245003)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010613872856 + 2 * 0.737676 / 12660) := by gcongr
    _ ≤ (0.052568060793 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12660 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12660

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12660
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501753657 : ℝ) ≤ plow 12660 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12660) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782785949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384895582) : eMP 12660 0.011 xi bn ≤ 0.001192202165 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12660 : ℝ) * (1 - 0.011))) ≤ 0.000589479188 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384895582 / (12660 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589479188 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589479188 : ℝ) + 3.141593 * 0.052782785949 / (12660 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192202165 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782785949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384895582) : PiBarMP 12660 12 0.011 xi bn ≤ 0.161507996769 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12660 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037214185226 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.896112533009 : ℝ) ≤ √((12660 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.516665432281 : ℝ) ≤ √(12660 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12660) ≤ 0.123825285875 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037214185226 + 0.052782785949 * 1.772454 / (2 * (111.896112533009 : ℝ))) * (1 + 0.001192202165) +
        8 / (12660 * 112.516665432281) + 0.123825285875 := by gcongr
    _ ≤ (0.161507996769 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782785949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384895582) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282313106331) :
    parallelOracle 12660 0.011 xi bn cd ≤ 0.162501376204 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12660 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12660 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501753657 : ℝ) ≤ plow 12660 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.516665432281 : ℝ) ≤ √(12660 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282313106331 : ℝ) / (2 * 0.560501753657 * 112.516665432281)) * 0.161507996769 +
        0.282313106331 ^ 2 / (2 * 0.560501753657 * 112.516665432281) := by gcongr
    _ ≤ (0.162501376204 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782785949) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384895582)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282313106331) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12660 12660 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501753657 : ℝ) ≤ plow 12660 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.516665432281 : ℝ) ≤ √(12660 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12660 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12660 Θ 1.22 ≤ 0.011785814083 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.516665432281 := by gcongr <;> linarith
      _ ≤ (0.011785814083 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12660 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12660 12660 0.011 ≤ 0.008495515194 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12660 12660 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12660 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12660 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12660 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12660 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162501376204 + 0.011785814083 + (0.008495515194 : ℝ) *
        (1 + 2 * (0.282313106331 + 0.011785814083) / (0.560501753657 * 112.516665432281))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12660]

end BstLean.Part269.N12660

/-! The original eight local profiles supply actual 12660 moment certificates. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12660 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052782785949 ∧
    0 ≤ bN 12660 BstLean.Part154.csC (groupTheta g) ∧ bN 12660 BstLean.Part154.csC (groupTheta g) ≤ 0.001384895582 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12660 12660 0.011
      (momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12660 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12660 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12660 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229745045538 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12660 0.011
      (momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12660 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12660
/-! The actual computed-centre upper energy formula at 12660. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12660

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12660)
open BstLean.Part268 (cell12660)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085607787013
  | 2 => 0.086552715636
  | 3 => 0.087496105044
  | 4 => 0.088439447052
  | 5 => 0.089384543610
  | 6 => 0.090333552557
  | 7 => 0.091289037600
  | 8 => 0.092254022585
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12660 12660 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12660 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12660

/-! Actual upper energy certificates on all 43 source endpoints at 12660. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12660)
open BstLean.Part268 (cell12660)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12660 (gMinus 12660) (1 - (cell12660 i).lower) ≤ 1 ∧
    energyUpper 12660 (gMinus 12660) (BstLean.Part211.gPlus 12660)
      (finiteEnergy 12660 12660 0.011) (1 - (cell12660 i).lower) ≤
      (cell12660 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨10,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨11,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨12,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨13,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨14,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨15,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨16,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨17,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨18,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨19,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨20,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨21,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨22,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨23,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨24,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨25,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨26,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨27,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨28,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨29,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨30,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨31,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨32,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨33,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨34,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨35,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨36,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨37,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨38,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨39,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨40,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨41,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨42,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨43,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨44,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨45,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨46,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨47,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨48,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨49,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨50,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨51,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12660) (by norm_num)
        (q := 1 - (cell12660 ⟨52,by decide⟩).lower)
        (by norm_num [cell12660]) (by norm_num [cell12660])
      exact ⟨E.1,E.2.trans (by norm_num [cell12660])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12660

/-! Source-cell containment and simple scalar guards at 12660. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12660)
open BstLean.Part268 (cell12660)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12660 ⟨10,by decide⟩).lower ∧ (cell12660 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12660 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12660 ⟨11,by decide⟩).lower ∧ (cell12660 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12660 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12660 ⟨12,by decide⟩).lower ∧ (cell12660 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12660 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12660 ⟨13,by decide⟩).lower ∧ (cell12660 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12660 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12660 ⟨14,by decide⟩).lower ∧ (cell12660 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12660 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12660 ⟨15,by decide⟩).lower ∧ (cell12660 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12660 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12660 ⟨16,by decide⟩).lower ∧ (cell12660 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12660 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12660 ⟨17,by decide⟩).lower ∧ (cell12660 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12660 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12660 ⟨18,by decide⟩).lower ∧ (cell12660 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12660 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12660 ⟨19,by decide⟩).lower ∧ (cell12660 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12660 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12660 ⟨20,by decide⟩).lower ∧ (cell12660 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12660 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12660 ⟨21,by decide⟩).lower ∧ (cell12660 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12660 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12660 ⟨22,by decide⟩).lower ∧ (cell12660 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12660 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12660 ⟨23,by decide⟩).lower ∧ (cell12660 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12660 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12660 ⟨24,by decide⟩).lower ∧ (cell12660 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12660 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12660 ⟨25,by decide⟩).lower ∧ (cell12660 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12660 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12660 ⟨26,by decide⟩).lower ∧ (cell12660 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12660 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12660 ⟨27,by decide⟩).lower ∧ (cell12660 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12660 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12660 ⟨28,by decide⟩).lower ∧ (cell12660 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12660 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12660 ⟨29,by decide⟩).lower ∧ (cell12660 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12660 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12660 ⟨30,by decide⟩).lower ∧ (cell12660 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12660 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12660 ⟨31,by decide⟩).lower ∧ (cell12660 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12660 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12660 ⟨32,by decide⟩).lower ∧ (cell12660 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12660 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12660 ⟨33,by decide⟩).lower ∧ (cell12660 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12660 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12660 ⟨34,by decide⟩).lower ∧ (cell12660 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12660 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12660 ⟨35,by decide⟩).lower ∧ (cell12660 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12660 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12660 ⟨36,by decide⟩).lower ∧ (cell12660 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12660 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12660 ⟨37,by decide⟩).lower ∧ (cell12660 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12660 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12660 ⟨38,by decide⟩).lower ∧ (cell12660 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12660 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12660 ⟨39,by decide⟩).lower ∧ (cell12660 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12660 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12660 ⟨40,by decide⟩).lower ∧ (cell12660 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12660 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12660 ⟨41,by decide⟩).lower ∧ (cell12660 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12660 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12660 ⟨42,by decide⟩).lower ∧ (cell12660 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12660 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12660 ⟨43,by decide⟩).lower ∧ (cell12660 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12660 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12660 ⟨44,by decide⟩).lower ∧ (cell12660 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12660 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12660 ⟨45,by decide⟩).lower ∧ (cell12660 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12660 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12660 ⟨46,by decide⟩).lower ∧ (cell12660 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12660 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12660 ⟨47,by decide⟩).lower ∧ (cell12660 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12660 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12660 ⟨48,by decide⟩).lower ∧ (cell12660 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12660 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12660 ⟨49,by decide⟩).lower ∧ (cell12660 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12660 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12660 ⟨50,by decide⟩).lower ∧ (cell12660 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12660 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12660 ⟨51,by decide⟩).lower ∧ (cell12660 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12660 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12660 ⟨52,by decide⟩).lower ∧ (cell12660 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12660 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12660 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12660 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12660,cell12660,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12660 i).lower ∧
    (cell12660 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12660 i).upper ≤ (0.532 : ℝ) ∧
    (cell12660 i).centre ≤ (0.1 : ℝ) ∧ (cell12660 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12660 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12660 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12660

/-! The local source numeric instances at 12660 have no network premises. -/
namespace BstLean.Part269.N12660
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12660)
open BstLean.Part268 (cell12660)

noncomputable def sourceNumerics12660 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12660 (cell12660 i)
      scalarRow12660.M scalarRow12660.H scalarRow12660.xi := by
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
    energy_allowance := scalarRow12660.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12660]
    centre_nonneg := (scalarRow12660.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12660])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12660
/-! Actual 12661 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12661 ≤ (1.035864816091 : ℝ) := by
  have hr : (112.521109130687 : ℝ) ≤ √(12661 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.521109130687 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12661 12661 (11 / 1000) ≤
    (0.008495179685 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12661) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.521109130687 : ℝ) ≤ √(12661 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12661)
  have hdiv : K / √(12661 : ℝ) ≤ K / 112.521109130687 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.521109130687 ≤ (0.008495179685 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12661.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12661 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12661 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12661 := gPlus_lower 12661
end BstLean.Part269.N12661

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12661
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035864816090 : ℝ) ≤ wn 12661 := by
  have hn : √(12661 : ℝ) ≤ 112.521109130688 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12661 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.521109130688 ≤ 2 / √(12661 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252670305 : ℝ) ≤ rhoBar 12661 BstLean.Part154.csC ∧
    rhoBar 12661 BstLean.Part154.csC ≤ 0.000252670696 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035864816090 : ℝ) / (1.295212 * 12661) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035864816091 : ℝ) / (1.29521 * 12661) := by gcongr
      _ ≤ (0.000252670696 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12661 BstLean.Part154.csC) ≤ 0.001010746627 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12661 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) ≤ 0.000192991610 ∧
    cc1 (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) ≤ 0.000122801837 ∧
    cc2 (rhoBar 12661 BstLean.Part154.csC) ≤ 0.000071287400 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12661 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12661 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12661 BstLean.Part154.csC * nuR (rhoBar 12661 BstLean.Part154.csC)) ≤ 0.000505357353 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252670696 : ℝ) * 0.001010746627 := by gcongr
      _ ≤ (0.000505357353 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12661 BstLean.Part154.csC) * nuR (rhoBar 12661 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010746627 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12661 BstLean.Part154.csC) * rhoBar 12661 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252670696 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252670696 / 2 + 0.399 * 0.001010746627 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192991610 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505357353 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122801837 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252670696 / 1.414213562 := by gcongr
      _ ≤ (0.000071287400 : ℝ) := by norm_num

end BstLean.Part269.N12661

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12661
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) ≤ 1.60847E-7 := by
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12661 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12661 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12661 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192991610 : ℝ) ^ 2 + 0.000122801837 ^ 2 + 3 * 0.000071287400 ^ 2 +
        2 * 0.797885 * 0.000192991610 * 0.000122801837 + 2 * 0.000192991610 * 0.000071287400 +
        4 * 0.797885 * 0.000122801837 * 0.000071287400 := by gcongr
    _ ≤ (1.60847E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12661 BstLean.Part154.csC Θ ≤ 0.002637678347 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12661 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12661 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12661 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035864816091 * 1.60847E-7 / (0.000252670305 : ℝ) := by gcongr
    _ ≤ 0.002637678347 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12661 BstLean.Part154.csC Θ ≤ 0.002926796158 + 0.000666496946 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12661 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12661 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035864816091 : ℝ) * ((2 * Θ * 0.000252670696 +
        (6863 / 10000) * 0.000252670696 * 12661 * 0.001010746627) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002926796158 + 0.000666496946 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12661 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12661 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12661 0.011 Θ ∧ gammaRatio 12661 0.011 Θ ≤ 0.000086861652 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12661 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035864816091 : ℝ) * 0.525 / ((1 - 0.011) * 12661) := by gcongr
      _ ≤ (0.000086861652 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12661 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12661 0.011 Θ) :=
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
    badAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12661 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12661 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12661 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12661 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12661 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12661 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12661 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12661 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12661 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12661 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035864816091 : ℝ) * 12661 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003541107549 + 0.003304175293 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12661

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12661
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12661 BstLean.Part154.csC) (piBar (rhoBar 12661 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12661 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12661 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12661 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12661 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12661 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12661 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12661 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12661 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12661 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12661 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052565962224 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12661) ≤ 0.010613453692 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12661 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035864816091)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010613453692 + 2 * 0.737676 / 12661) := by gcongr
    _ ≤ (0.052565962224 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12661 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12661

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12661
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501799162 : ℝ) ≤ plow 12661 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12661) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782399578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384781133) : eMP 12661 0.011 xi bn ≤ 0.001192105750 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12661 : ℝ) * (1 - 0.011))) ≤ 0.000589431552 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384781133 / (12661 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589431552 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589431552 : ℝ) + 3.141593 * 0.052782399578 / (12661 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192105750 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782399578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384781133) : PiBarMP 12661 12 0.011 xi bn ≤ 0.161501543186 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12661 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037212647488 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.900531723490 : ℝ) ≤ √((12661 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.521109130687 : ℝ) ≤ √(12661 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12661) ≤ 0.123820395750 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037212647488 + 0.052782399578 * 1.772454 / (2 * (111.900531723490 : ℝ))) * (1 + 0.001192105750) +
        8 / (12661 * 112.521109130687) + 0.123820395750 := by gcongr
    _ ≤ (0.161501543186 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782399578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384781133) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282310166891) :
    parallelOracle 12661 0.011 xi bn cd ≤ 0.162494851945 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12661 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12661 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501799162 : ℝ) ≤ plow 12661 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.521109130687 : ℝ) ≤ √(12661 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282310166891 : ℝ) / (2 * 0.560501799162 * 112.521109130687)) * 0.161501543186 +
        0.282310166891 ^ 2 / (2 * 0.560501799162 * 112.521109130687) := by gcongr
    _ ≤ (0.162494851945 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782399578) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384781133)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282310166891) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12661 12661 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501799162 : ℝ) ≤ plow 12661 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.521109130687 : ℝ) ≤ √(12661 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12661 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12661 Θ 1.22 ≤ 0.011785348636 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.521109130687 := by gcongr <;> linarith
      _ ≤ (0.011785348636 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12661 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12661 12661 0.011 ≤ 0.008495179685 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12661 12661 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12661 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12661 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12661 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12661 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162494851945 + 0.011785348636 + (0.008495179685 : ℝ) *
        (1 + 2 * (0.282310166891 + 0.011785348636) / (0.560501799162 * 112.521109130687))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12661]

end BstLean.Part269.N12661

/-! The original eight local profiles supply actual 12661 moment certificates. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12661 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052782399578 ∧
    0 ≤ bN 12661 BstLean.Part154.csC (groupTheta g) ∧ bN 12661 BstLean.Part154.csC (groupTheta g) ≤ 0.001384781133 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12661 12661 0.011
      (momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12661 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12661 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12661 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229744204667 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12661 0.011
      (momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12661 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12661
/-! The actual computed-centre upper energy formula at 12661. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12661

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12661)
open BstLean.Part268 (cell12661)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085604827031
  | 2 => 0.086549700272
  | 3 => 0.087493026059
  | 4 => 0.088436294319
  | 5 => 0.089381304785
  | 6 => 0.090330212707
  | 7 => 0.091285578789
  | 8 => 0.092250423410
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12661 12661 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12661 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12661

/-! Actual upper energy certificates on all 43 source endpoints at 12661. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12661)
open BstLean.Part268 (cell12661)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12661 (gMinus 12661) (1 - (cell12661 i).lower) ≤ 1 ∧
    energyUpper 12661 (gMinus 12661) (BstLean.Part211.gPlus 12661)
      (finiteEnergy 12661 12661 0.011) (1 - (cell12661 i).lower) ≤
      (cell12661 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨10,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨11,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨12,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨13,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨14,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨15,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨16,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨17,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨18,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨19,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨20,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨21,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨22,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨23,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨24,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨25,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨26,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨27,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨28,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨29,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨30,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨31,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨32,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨33,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨34,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨35,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨36,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨37,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨38,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨39,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨40,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨41,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨42,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨43,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨44,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨45,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨46,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨47,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨48,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨49,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨50,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨51,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12661) (by norm_num)
        (q := 1 - (cell12661 ⟨52,by decide⟩).lower)
        (by norm_num [cell12661]) (by norm_num [cell12661])
      exact ⟨E.1,E.2.trans (by norm_num [cell12661])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12661

/-! Source-cell containment and simple scalar guards at 12661. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12661)
open BstLean.Part268 (cell12661)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12661 ⟨10,by decide⟩).lower ∧ (cell12661 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12661 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12661 ⟨11,by decide⟩).lower ∧ (cell12661 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12661 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12661 ⟨12,by decide⟩).lower ∧ (cell12661 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12661 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12661 ⟨13,by decide⟩).lower ∧ (cell12661 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12661 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12661 ⟨14,by decide⟩).lower ∧ (cell12661 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12661 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12661 ⟨15,by decide⟩).lower ∧ (cell12661 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12661 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12661 ⟨16,by decide⟩).lower ∧ (cell12661 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12661 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12661 ⟨17,by decide⟩).lower ∧ (cell12661 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12661 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12661 ⟨18,by decide⟩).lower ∧ (cell12661 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12661 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12661 ⟨19,by decide⟩).lower ∧ (cell12661 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12661 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12661 ⟨20,by decide⟩).lower ∧ (cell12661 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12661 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12661 ⟨21,by decide⟩).lower ∧ (cell12661 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12661 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12661 ⟨22,by decide⟩).lower ∧ (cell12661 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12661 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12661 ⟨23,by decide⟩).lower ∧ (cell12661 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12661 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12661 ⟨24,by decide⟩).lower ∧ (cell12661 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12661 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12661 ⟨25,by decide⟩).lower ∧ (cell12661 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12661 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12661 ⟨26,by decide⟩).lower ∧ (cell12661 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12661 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12661 ⟨27,by decide⟩).lower ∧ (cell12661 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12661 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12661 ⟨28,by decide⟩).lower ∧ (cell12661 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12661 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12661 ⟨29,by decide⟩).lower ∧ (cell12661 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12661 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12661 ⟨30,by decide⟩).lower ∧ (cell12661 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12661 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12661 ⟨31,by decide⟩).lower ∧ (cell12661 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12661 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12661 ⟨32,by decide⟩).lower ∧ (cell12661 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12661 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12661 ⟨33,by decide⟩).lower ∧ (cell12661 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12661 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12661 ⟨34,by decide⟩).lower ∧ (cell12661 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12661 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12661 ⟨35,by decide⟩).lower ∧ (cell12661 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12661 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12661 ⟨36,by decide⟩).lower ∧ (cell12661 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12661 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12661 ⟨37,by decide⟩).lower ∧ (cell12661 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12661 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12661 ⟨38,by decide⟩).lower ∧ (cell12661 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12661 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12661 ⟨39,by decide⟩).lower ∧ (cell12661 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12661 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12661 ⟨40,by decide⟩).lower ∧ (cell12661 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12661 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12661 ⟨41,by decide⟩).lower ∧ (cell12661 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12661 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12661 ⟨42,by decide⟩).lower ∧ (cell12661 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12661 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12661 ⟨43,by decide⟩).lower ∧ (cell12661 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12661 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12661 ⟨44,by decide⟩).lower ∧ (cell12661 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12661 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12661 ⟨45,by decide⟩).lower ∧ (cell12661 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12661 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12661 ⟨46,by decide⟩).lower ∧ (cell12661 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12661 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12661 ⟨47,by decide⟩).lower ∧ (cell12661 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12661 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12661 ⟨48,by decide⟩).lower ∧ (cell12661 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12661 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12661 ⟨49,by decide⟩).lower ∧ (cell12661 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12661 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12661 ⟨50,by decide⟩).lower ∧ (cell12661 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12661 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12661 ⟨51,by decide⟩).lower ∧ (cell12661 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12661 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12661 ⟨52,by decide⟩).lower ∧ (cell12661 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12661 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12661 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12661 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12661,cell12661,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12661 i).lower ∧
    (cell12661 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12661 i).upper ≤ (0.532 : ℝ) ∧
    (cell12661 i).centre ≤ (0.1 : ℝ) ∧ (cell12661 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12661 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12661 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12661

/-! The local source numeric instances at 12661 have no network premises. -/
namespace BstLean.Part269.N12661
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12661)
open BstLean.Part268 (cell12661)

noncomputable def sourceNumerics12661 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12661 (cell12661 i)
      scalarRow12661.M scalarRow12661.H scalarRow12661.xi := by
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
    energy_allowance := scalarRow12661.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12661]
    centre_nonneg := (scalarRow12661.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12661])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12661
/-! Actual 12662 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12662 ≤ (1.035863387350 : ℝ) := by
  have hr : (112.525552653608 : ℝ) ≤ √(12662 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.525552653608 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12662 12662 (11 / 1000) ≤
    (0.008494844216 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12662) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.525552653608 : ℝ) ≤ √(12662 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12662)
  have hdiv : K / √(12662 : ℝ) ≤ K / 112.525552653608 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.525552653608 ≤ (0.008494844216 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12662.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12662 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12662 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12662 := gPlus_lower 12662
end BstLean.Part269.N12662

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12662
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035863387349 : ℝ) ≤ wn 12662 := by
  have hn : √(12662 : ℝ) ≤ 112.525552653609 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12662 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.525552653609 ≤ 2 / √(12662 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252650001 : ℝ) ≤ rhoBar 12662 BstLean.Part154.csC ∧
    rhoBar 12662 BstLean.Part154.csC ≤ 0.000252650393 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035863387349 : ℝ) / (1.295212 * 12662) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035863387350 : ℝ) / (1.29521 * 12662) := by gcongr
      _ ≤ (0.000252650393 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12662 BstLean.Part154.csC) ≤ 0.001010665405 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12662 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) ≤ 0.000192976102 ∧
    cc1 (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) ≤ 0.000122791969 ∧
    cc2 (rhoBar 12662 BstLean.Part154.csC) ≤ 0.000071281672 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12662 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12662 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12662 BstLean.Part154.csC * nuR (rhoBar 12662 BstLean.Part154.csC)) ≤ 0.000505316744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252650393 : ℝ) * 0.001010665405 := by gcongr
      _ ≤ (0.000505316744 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12662 BstLean.Part154.csC) * nuR (rhoBar 12662 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010665405 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12662 BstLean.Part154.csC) * rhoBar 12662 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252650393 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252650393 / 2 + 0.399 * 0.001010665405 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192976102 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505316744 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122791969 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252650393 / 1.414213562 := by gcongr
      _ ≤ (0.000071281672 : ℝ) := by norm_num

end BstLean.Part269.N12662

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12662
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) ≤ 1.60821E-7 := by
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12662 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12662 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12662 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192976102 : ℝ) ^ 2 + 0.000122791969 ^ 2 + 3 * 0.000071281672 ^ 2 +
        2 * 0.797885 * 0.000192976102 * 0.000122791969 + 2 * 0.000192976102 * 0.000071281672 +
        4 * 0.797885 * 0.000122791969 * 0.000071281672 := by gcongr
    _ ≤ (1.60821E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12662 BstLean.Part154.csC Θ ≤ 0.002637460284 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12662 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12662 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12662 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035863387350 * 1.60821E-7 / (0.000252650001 : ℝ) := by gcongr
    _ ≤ 0.002637460284 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12662 BstLean.Part154.csC Θ ≤ 0.002926552898 + 0.000666442471 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12662 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12662 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035863387350 : ℝ) * ((2 * Θ * 0.000252650393 +
        (6863 / 10000) * 0.000252650393 * 12662 * 0.001010665405) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002926552898 + 0.000666442471 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12662 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12662 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12662 0.011 Θ ∧ gammaRatio 12662 0.011 Θ ≤ 0.000086854672 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12662 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035863387350 : ℝ) * 0.525 / ((1 - 0.011) * 12662) := by gcongr
      _ ≤ (0.000086854672 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12662 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12662 0.011 Θ) :=
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
    badAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12662 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12662 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12662 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12662 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12662 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12662 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12662 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12662 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12662 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12662 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035863387350 : ℝ) * 12662 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003540864289 + 0.003303902755 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12662

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12662
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12662 BstLean.Part154.csC) (piBar (rhoBar 12662 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12662 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12662 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12662 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12662 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12662 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12662 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12662 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12662 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12662 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12662 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052563863904 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12662) ≤ 0.010613034577 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12662 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035863387350)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010613034577 + 2 * 0.737676 / 12662) := by gcongr
    _ ≤ (0.052563863904 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12662 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12662

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12662
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501844661 : ℝ) ≤ plow 12662 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12662) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782013236)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384666650) : eMP 12662 0.011 xi bn ≤ 0.001192009325 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12662 : ℝ) * (1 - 0.011))) ≤ 0.000589383911 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384666650 / (12662 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589383911 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589383911 : ℝ) + 3.141593 * 0.052782013236 / (12662 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001192009325 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782013236)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384666650) : PiBarMP 12662 12 0.011 xi bn ≤ 0.161495089664 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12662 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037211109229 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.904950739455 : ℝ) ≤ √((12662 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.525552653608 : ℝ) ≤ √(12662 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12662) ≤ 0.123815506205 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037211109229 + 0.052782013236 * 1.772454 / (2 * (111.904950739455 : ℝ))) * (1 + 0.001192009325) +
        8 / (12662 * 112.525552653608) + 0.123815506205 := by gcongr
    _ ≤ (0.161495089664 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782013236)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384666650) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282307227761) :
    parallelOracle 12662 0.011 xi bn cd ≤ 0.162488327755 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12662 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12662 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501844661 : ℝ) ≤ plow 12662 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.525552653608 : ℝ) ≤ √(12662 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282307227761 : ℝ) / (2 * 0.560501844661 * 112.525552653608)) * 0.161495089664 +
        0.282307227761 ^ 2 / (2 * 0.560501844661 * 112.525552653608) := by gcongr
    _ ≤ (0.162488327755 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052782013236) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384666650)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282307227761) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12662 12662 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501844661 : ℝ) ≤ plow 12662 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.525552653608 : ℝ) ≤ √(12662 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12662 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12662 Θ 1.22 ≤ 0.011784883245 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.525552653608 := by gcongr <;> linarith
      _ ≤ (0.011784883245 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12662 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12662 12662 0.011 ≤ 0.008494844216 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12662 12662 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12662 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12662 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12662 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12662 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162488327755 + 0.011784883245 + (0.008494844216 : ℝ) *
        (1 + 2 * (0.282307227761 + 0.011784883245) / (0.560501844661 * 112.525552653608))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12662]

end BstLean.Part269.N12662

/-! The original eight local profiles supply actual 12662 moment certificates. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12662 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052782013236 ∧
    0 ≤ bN 12662 BstLean.Part154.csC (groupTheta g) ∧ bN 12662 BstLean.Part154.csC (groupTheta g) ≤ 0.001384666650 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12662 12662 0.011
      (momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12662 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12662 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12662 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229743363857 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12662 0.011
      (momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12662 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12662
/-! The actual computed-centre upper energy formula at 12662. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12662

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12662)
open BstLean.Part268 (cell12662)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085601868177
  | 2 => 0.086546686084
  | 3 => 0.087489948307
  | 4 => 0.088433142889
  | 5 => 0.089378067351
  | 6 => 0.090326874353
  | 7 => 0.091282121600
  | 8 => 0.092246826012
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12662 12662 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12662 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12662

/-! Actual upper energy certificates on all 43 source endpoints at 12662. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12662)
open BstLean.Part268 (cell12662)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12662 (gMinus 12662) (1 - (cell12662 i).lower) ≤ 1 ∧
    energyUpper 12662 (gMinus 12662) (BstLean.Part211.gPlus 12662)
      (finiteEnergy 12662 12662 0.011) (1 - (cell12662 i).lower) ≤
      (cell12662 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨10,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨11,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨12,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨13,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨14,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨15,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨16,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨17,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨18,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨19,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨20,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨21,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨22,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨23,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨24,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨25,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨26,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨27,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨28,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨29,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨30,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨31,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨32,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨33,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨34,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨35,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨36,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨37,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨38,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨39,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨40,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨41,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨42,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨43,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨44,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨45,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨46,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨47,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨48,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨49,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨50,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨51,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12662) (by norm_num)
        (q := 1 - (cell12662 ⟨52,by decide⟩).lower)
        (by norm_num [cell12662]) (by norm_num [cell12662])
      exact ⟨E.1,E.2.trans (by norm_num [cell12662])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12662

/-! Source-cell containment and simple scalar guards at 12662. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12662)
open BstLean.Part268 (cell12662)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12662 ⟨10,by decide⟩).lower ∧ (cell12662 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12662 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12662 ⟨11,by decide⟩).lower ∧ (cell12662 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12662 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12662 ⟨12,by decide⟩).lower ∧ (cell12662 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12662 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12662 ⟨13,by decide⟩).lower ∧ (cell12662 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12662 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12662 ⟨14,by decide⟩).lower ∧ (cell12662 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12662 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12662 ⟨15,by decide⟩).lower ∧ (cell12662 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12662 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12662 ⟨16,by decide⟩).lower ∧ (cell12662 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12662 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12662 ⟨17,by decide⟩).lower ∧ (cell12662 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12662 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12662 ⟨18,by decide⟩).lower ∧ (cell12662 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12662 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12662 ⟨19,by decide⟩).lower ∧ (cell12662 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12662 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12662 ⟨20,by decide⟩).lower ∧ (cell12662 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12662 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12662 ⟨21,by decide⟩).lower ∧ (cell12662 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12662 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12662 ⟨22,by decide⟩).lower ∧ (cell12662 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12662 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12662 ⟨23,by decide⟩).lower ∧ (cell12662 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12662 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12662 ⟨24,by decide⟩).lower ∧ (cell12662 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12662 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12662 ⟨25,by decide⟩).lower ∧ (cell12662 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12662 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12662 ⟨26,by decide⟩).lower ∧ (cell12662 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12662 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12662 ⟨27,by decide⟩).lower ∧ (cell12662 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12662 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12662 ⟨28,by decide⟩).lower ∧ (cell12662 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12662 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12662 ⟨29,by decide⟩).lower ∧ (cell12662 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12662 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12662 ⟨30,by decide⟩).lower ∧ (cell12662 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12662 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12662 ⟨31,by decide⟩).lower ∧ (cell12662 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12662 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12662 ⟨32,by decide⟩).lower ∧ (cell12662 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12662 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12662 ⟨33,by decide⟩).lower ∧ (cell12662 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12662 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12662 ⟨34,by decide⟩).lower ∧ (cell12662 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12662 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12662 ⟨35,by decide⟩).lower ∧ (cell12662 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12662 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12662 ⟨36,by decide⟩).lower ∧ (cell12662 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12662 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12662 ⟨37,by decide⟩).lower ∧ (cell12662 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12662 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12662 ⟨38,by decide⟩).lower ∧ (cell12662 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12662 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12662 ⟨39,by decide⟩).lower ∧ (cell12662 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12662 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12662 ⟨40,by decide⟩).lower ∧ (cell12662 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12662 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12662 ⟨41,by decide⟩).lower ∧ (cell12662 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12662 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12662 ⟨42,by decide⟩).lower ∧ (cell12662 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12662 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12662 ⟨43,by decide⟩).lower ∧ (cell12662 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12662 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12662 ⟨44,by decide⟩).lower ∧ (cell12662 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12662 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12662 ⟨45,by decide⟩).lower ∧ (cell12662 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12662 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12662 ⟨46,by decide⟩).lower ∧ (cell12662 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12662 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12662 ⟨47,by decide⟩).lower ∧ (cell12662 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12662 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12662 ⟨48,by decide⟩).lower ∧ (cell12662 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12662 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12662 ⟨49,by decide⟩).lower ∧ (cell12662 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12662 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12662 ⟨50,by decide⟩).lower ∧ (cell12662 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12662 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12662 ⟨51,by decide⟩).lower ∧ (cell12662 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12662 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12662 ⟨52,by decide⟩).lower ∧ (cell12662 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12662 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12662 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12662 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12662,cell12662,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12662 i).lower ∧
    (cell12662 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12662 i).upper ≤ (0.532 : ℝ) ∧
    (cell12662 i).centre ≤ (0.1 : ℝ) ∧ (cell12662 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12662 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12662 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12662

/-! The local source numeric instances at 12662 have no network premises. -/
namespace BstLean.Part269.N12662
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12662)
open BstLean.Part268 (cell12662)

noncomputable def sourceNumerics12662 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12662 (cell12662 i)
      scalarRow12662.M scalarRow12662.H scalarRow12662.xi := by
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
    energy_allowance := scalarRow12662.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12662]
    centre_nonneg := (scalarRow12662.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12662])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12662