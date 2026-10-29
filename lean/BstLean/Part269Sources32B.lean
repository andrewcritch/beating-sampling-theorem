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
import BstLean.Part269Direction32
import BstLean.Part269Shared32
import BstLean.Part269Finite
import BstLean.Part269Rows32
import BstLean.Part269Source
/-! Actual 13163 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13163 ≤ (1.035168310599 : ℝ) := by
  have hr : (114.730118103312 : ℝ) ≤ √(13163 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.730118103312 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13163 13163 (11 / 1000) ≤
    (0.008331612620 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13163) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.730118103312 : ℝ) ≤ √(13163 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13163)
  have hdiv : K / √(13163 : ℝ) ≤ K / 114.730118103312 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.730118103312 ≤ (0.008331612620 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13163.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13163 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13163 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13163 := gPlus_lower 13163
end BstLean.Part269.N13163

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13163
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035168310598 : ℝ) ≤ wn 13163 := by
  have hn : √(13163 : ℝ) ≤ 114.730118103313 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13163 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.730118103313 ≤ 2 / √(13163 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242870752 : ℝ) ≤ rhoBar 13163 BstLean.Part154.csC ∧
    rhoBar 13163 BstLean.Part154.csC ≤ 0.000242871128 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035168310598 : ℝ) / (1.295212 * 13163) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035168310599 : ℝ) / (1.29521 * 13163) := by gcongr
      _ ≤ (0.000242871128 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13163 BstLean.Part154.csC) ≤ 0.000971543499 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13163 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) ≤ 0.000185506297 ∧
    cc1 (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) ≤ 0.000118038952 ∧
    cc2 (rhoBar 13163 BstLean.Part154.csC) ≤ 0.000068522593 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13163 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13163 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13163 BstLean.Part154.csC * nuR (rhoBar 13163 BstLean.Part154.csC)) ≤ 0.000485757003 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242871128 : ℝ) * 0.000971543499 := by gcongr
      _ ≤ (0.000485757003 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13163 BstLean.Part154.csC) * nuR (rhoBar 13163 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971543499 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13163 BstLean.Part154.csC) * rhoBar 13163 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242871128 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242871128 / 2 + 0.399 * 0.000971543499 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185506297 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485757003 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118038952 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242871128 / 1.414213562 := by gcongr
      _ ≤ (0.000068522593 : ℝ) := by norm_num

end BstLean.Part269.N13163

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13163
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) ≤ 1.48612E-7 := by
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13163 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13163 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13163 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185506297 : ℝ) ^ 2 + 0.000118038952 ^ 2 + 3 * 0.000068522593 ^ 2 +
        2 * 0.797885 * 0.000185506297 * 0.000118038952 + 2 * 0.000185506297 * 0.000068522593 +
        4 * 0.797885 * 0.000118038952 * 0.000068522593 := by gcongr
    _ ≤ (1.48612E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13163 BstLean.Part154.csC Θ ≤ 0.002533667504 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13163 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13163 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13163 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035168310599 * 1.48612E-7 / (0.000242870752 : ℝ) := by gcongr
    _ ≤ 0.002533667504 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13163 BstLean.Part154.csC Θ ≤ 0.002809494575 + 0.000640216796 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13163 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13163 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035168310599 : ℝ) * ((2 * Θ * 0.000242871128 +
        (6863 / 10000) * 0.000242871128 * 13163 * 0.000971543499) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002809494575 + 0.000640216796 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13163 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13163 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13163 0.011 Θ ∧ gammaRatio 13163 0.011 Θ ≤ 0.000083492814 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13163 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035168310599 : ℝ) * 0.525 / ((1 - 0.011) * 13163) := by gcongr
      _ ≤ (0.000083492814 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13163 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13163 0.011 Θ) :=
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
    badAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13163 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13163 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13163 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13163 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13163 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13163 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13163 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13163 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13163 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13163 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035168310599 : ℝ) * 13163 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003126379733 + 0.003173884300 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13163

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13163
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13163 BstLean.Part154.csC) (piBar (rhoBar 13163 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13163 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13163 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13163 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13163 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13163 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13163 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13163 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13163 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13163 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13163 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051543079569 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13163) ≤ 0.010409102691 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13163 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035168310599)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010409102691 + 2 * 0.737676 / 13163) := by gcongr
    _ ≤ (0.051543079569 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13163 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13163

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13163
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523770037 : ℝ) ≤ plow 13163 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13163) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299268991)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330175440) : eMP 13163 0.011 xi bn ≤ 0.001145761702 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13163 : ℝ) * (1 - 0.011))) ≤ 0.000566570342 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330175440 / (13163 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566570342 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566570342 : ℝ) + 3.141593 * 0.052299268991 / (13163 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145761702 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299268991)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330175440) : PiBarMP 13163 12 0.011 xi bn ≤ 0.158361707214 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13163 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036471570298 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.097357550470 : ℝ) ≤ √((13163 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.730118103312 : ℝ) ≤ √(13163 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13163) ≤ 0.121436362946 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036471570298 + 0.052299268991 * 1.772454 / (2 * (114.097357550470 : ℝ))) * (1 + 0.001145761702) +
        8 / (13163 * 114.730118103312) + 0.121436362946 := by gcongr
    _ ≤ (0.158361707214 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299268991)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330175440) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280233413845) :
    parallelOracle 13163 0.011 xi bn cd ≤ 0.159317320641 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13163 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13163 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523770037 : ℝ) ≤ plow 13163 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.730118103312 : ℝ) ≤ √(13163 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280233413845 : ℝ) / (2 * 0.560523770037 * 114.730118103312)) * 0.158361707214 +
        0.280233413845 ^ 2 / (2 * 0.560523770037 * 114.730118103312) := by gcongr
    _ ≤ (0.159317320641 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299268991) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330175440)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280233413845) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13163 13163 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523770037 : ℝ) ≤ plow 13163 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.730118103312 : ℝ) ≤ √(13163 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13163 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13163 Θ 1.22 ≤ 0.011558434019 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.730118103312 := by gcongr <;> linarith
      _ ≤ (0.011558434019 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13163 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13163 13163 0.011 ≤ 0.008331612620 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13163 13163 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13163 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13163 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13163 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13163 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159317320641 + 0.011558434019 + (0.008331612620 : ℝ) *
        (1 + 2 * (0.280233413845 + 0.011558434019) / (0.560523770037 * 114.730118103312))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13163]

end BstLean.Part269.N13163

/-! The original eight local profiles supply actual 13163 moment certificates. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13163 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052299268991 ∧
    0 ≤ bN 13163 BstLean.Part154.csC (groupTheta g) ∧ bN 13163 BstLean.Part154.csC (groupTheta g) ≤ 0.001330175440 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13163 13163 0.011
      (momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13163 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13163 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13163 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228690334276 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13163 0.011
      (momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13163 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13163
/-! The actual computed-centre upper energy formula at 13163. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13163

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13163)
open BstLean.Part268 (cell13163)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084243496784
  | 2 => 0.085166890398
  | 3 => 0.086085721077
  | 4 => 0.087000770301
  | 5 => 0.087913001225
  | 6 => 0.088823587826
  | 7 => 0.089733947214
  | 8 => 0.090645775228
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13163 13163 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13163 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13163

/-! Actual upper energy certificates on all 43 source endpoints at 13163. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13163)
open BstLean.Part268 (cell13163)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13163 (gMinus 13163) (1 - (cell13163 i).lower) ≤ 1 ∧
    energyUpper 13163 (gMinus 13163) (BstLean.Part211.gPlus 13163)
      (finiteEnergy 13163 13163 0.011) (1 - (cell13163 i).lower) ≤
      (cell13163 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨10,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨11,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨12,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨13,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨14,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨15,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨16,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨17,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨18,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨19,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨20,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨21,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨22,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨23,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨24,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨25,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨26,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨27,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨28,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨29,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨30,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨31,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨32,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨33,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨34,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨35,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨36,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨37,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨38,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨39,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨40,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨41,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨42,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨43,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨44,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨45,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨46,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨47,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨48,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨49,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨50,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨51,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13163) (by norm_num)
        (q := 1 - (cell13163 ⟨52,by decide⟩).lower)
        (by norm_num [cell13163]) (by norm_num [cell13163])
      exact ⟨E.1,E.2.trans (by norm_num [cell13163])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13163

/-! Source-cell containment and simple scalar guards at 13163. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13163)
open BstLean.Part268 (cell13163)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13163 ⟨10,by decide⟩).lower ∧ (cell13163 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13163 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13163 ⟨11,by decide⟩).lower ∧ (cell13163 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13163 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13163 ⟨12,by decide⟩).lower ∧ (cell13163 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13163 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13163 ⟨13,by decide⟩).lower ∧ (cell13163 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13163 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13163 ⟨14,by decide⟩).lower ∧ (cell13163 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13163 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13163 ⟨15,by decide⟩).lower ∧ (cell13163 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13163 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13163 ⟨16,by decide⟩).lower ∧ (cell13163 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13163 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13163 ⟨17,by decide⟩).lower ∧ (cell13163 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13163 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13163 ⟨18,by decide⟩).lower ∧ (cell13163 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13163 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13163 ⟨19,by decide⟩).lower ∧ (cell13163 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13163 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13163 ⟨20,by decide⟩).lower ∧ (cell13163 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13163 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13163 ⟨21,by decide⟩).lower ∧ (cell13163 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13163 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13163 ⟨22,by decide⟩).lower ∧ (cell13163 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13163 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13163 ⟨23,by decide⟩).lower ∧ (cell13163 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13163 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13163 ⟨24,by decide⟩).lower ∧ (cell13163 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13163 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13163 ⟨25,by decide⟩).lower ∧ (cell13163 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13163 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13163 ⟨26,by decide⟩).lower ∧ (cell13163 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13163 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13163 ⟨27,by decide⟩).lower ∧ (cell13163 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13163 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13163 ⟨28,by decide⟩).lower ∧ (cell13163 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13163 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13163 ⟨29,by decide⟩).lower ∧ (cell13163 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13163 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13163 ⟨30,by decide⟩).lower ∧ (cell13163 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13163 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13163 ⟨31,by decide⟩).lower ∧ (cell13163 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13163 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13163 ⟨32,by decide⟩).lower ∧ (cell13163 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13163 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13163 ⟨33,by decide⟩).lower ∧ (cell13163 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13163 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13163 ⟨34,by decide⟩).lower ∧ (cell13163 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13163 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13163 ⟨35,by decide⟩).lower ∧ (cell13163 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13163 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13163 ⟨36,by decide⟩).lower ∧ (cell13163 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13163 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13163 ⟨37,by decide⟩).lower ∧ (cell13163 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13163 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13163 ⟨38,by decide⟩).lower ∧ (cell13163 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13163 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13163 ⟨39,by decide⟩).lower ∧ (cell13163 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13163 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13163 ⟨40,by decide⟩).lower ∧ (cell13163 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13163 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13163 ⟨41,by decide⟩).lower ∧ (cell13163 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13163 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13163 ⟨42,by decide⟩).lower ∧ (cell13163 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13163 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13163 ⟨43,by decide⟩).lower ∧ (cell13163 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13163 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13163 ⟨44,by decide⟩).lower ∧ (cell13163 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13163 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13163 ⟨45,by decide⟩).lower ∧ (cell13163 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13163 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13163 ⟨46,by decide⟩).lower ∧ (cell13163 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13163 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13163 ⟨47,by decide⟩).lower ∧ (cell13163 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13163 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13163 ⟨48,by decide⟩).lower ∧ (cell13163 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13163 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13163 ⟨49,by decide⟩).lower ∧ (cell13163 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13163 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13163 ⟨50,by decide⟩).lower ∧ (cell13163 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13163 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13163 ⟨51,by decide⟩).lower ∧ (cell13163 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13163 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13163 ⟨52,by decide⟩).lower ∧ (cell13163 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13163 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13163 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13163 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13163,cell13163,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13163 i).lower ∧
    (cell13163 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13163 i).upper ≤ (0.532 : ℝ) ∧
    (cell13163 i).centre ≤ (0.1 : ℝ) ∧ (cell13163 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13163 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13163 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13163

/-! The local source numeric instances at 13163 have no network premises. -/
namespace BstLean.Part269.N13163
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13163)
open BstLean.Part268 (cell13163)

noncomputable def sourceNumerics13163 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13163 (cell13163 i)
      scalarRow13163.M scalarRow13163.H scalarRow13163.xi := by
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
    energy_allowance := scalarRow13163.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13163]
    centre_nonneg := (scalarRow13163.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13163])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13163
/-! Actual 13164 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13164 ≤ (1.035166963256 : ℝ) := by
  have hr : (114.734476074107 : ℝ) ≤ √(13164 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.734476074107 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13164 13164 (11 / 1000) ≤
    (0.008331296157 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13164) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.734476074107 : ℝ) ≤ √(13164 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13164)
  have hdiv : K / √(13164 : ℝ) ≤ K / 114.734476074107 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.734476074107 ≤ (0.008331296157 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13164.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13164 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13164 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13164 := gPlus_lower 13164
end BstLean.Part269.N13164

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13164
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035166963255 : ℝ) ≤ wn 13164 := by
  have hn : √(13164 : ℝ) ≤ 114.734476074108 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13164 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.734476074108 ≤ 2 / √(13164 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242851987 : ℝ) ≤ rhoBar 13164 BstLean.Part154.csC ∧
    rhoBar 13164 BstLean.Part154.csC ≤ 0.000242852363 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035166963255 : ℝ) / (1.295212 * 13164) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035166963256 : ℝ) / (1.29521 * 13164) := by gcongr
      _ ≤ (0.000242852363 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13164 BstLean.Part154.csC) ≤ 0.000971468430 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13164 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) ≤ 0.000185491964 ∧
    cc1 (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) ≤ 0.000118029832 ∧
    cc2 (rhoBar 13164 BstLean.Part154.csC) ≤ 0.000068517299 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13164 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13164 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13164 BstLean.Part154.csC * nuR (rhoBar 13164 BstLean.Part154.csC)) ≤ 0.000485719471 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242852363 : ℝ) * 0.000971468430 := by gcongr
      _ ≤ (0.000485719471 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13164 BstLean.Part154.csC) * nuR (rhoBar 13164 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971468430 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13164 BstLean.Part154.csC) * rhoBar 13164 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242852363 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242852363 / 2 + 0.399 * 0.000971468430 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185491964 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485719471 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118029832 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242852363 / 1.414213562 := by gcongr
      _ ≤ (0.000068517299 : ℝ) := by norm_num

end BstLean.Part269.N13164

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13164
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) ≤ 1.48589E-7 := by
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13164 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13164 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13164 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185491964 : ℝ) ^ 2 + 0.000118029832 ^ 2 + 3 * 0.000068517299 ^ 2 +
        2 * 0.797885 * 0.000185491964 * 0.000118029832 + 2 * 0.000185491964 * 0.000068517299 +
        4 * 0.797885 * 0.000118029832 * 0.000068517299 := by gcongr
    _ ≤ (1.48589E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13164 BstLean.Part154.csC Θ ≤ 0.002533467827 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13164 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13164 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13164 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035166963256 * 1.48589E-7 / (0.000242851987 : ℝ) := by gcongr
    _ ≤ 0.002533467827 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13164 BstLean.Part154.csC Θ ≤ 0.002809270187 + 0.000640166497 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13164 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13164 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035166963256 : ℝ) * ((2 * Θ * 0.000242852363 +
        (6863 / 10000) * 0.000242852363 * 13164 * 0.000971468430) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002809270187 + 0.000640166497 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13164 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13164 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13164 0.011 Θ ∧ gammaRatio 13164 0.011 Θ ≤ 0.000083486363 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13164 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035166963256 : ℝ) * 0.525 / ((1 - 0.011) * 13164) := by gcongr
      _ ≤ (0.000083486363 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13164 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13164 0.011 Θ) :=
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
    badAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13164 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13164 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13164 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13164 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13164 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13164 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13164 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13164 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13164 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13164 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035166963256 : ℝ) * 13164 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003126155345 + 0.003173634324 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13164

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13164
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13164 BstLean.Part154.csC) (piBar (rhoBar 13164 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13164 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13164 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13164 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13164 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13164 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13164 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13164 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13164 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13164 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13164 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051541100947 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13164) ≤ 0.010408707321 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13164 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035166963256)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010408707321 + 2 * 0.737676 / 13164) := by gcongr
    _ ≤ (0.051541100947 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13164 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13164

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13164
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523812131 : ℝ) ≤ plow 13164 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13164) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298913366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330070610) : eMP 13164 0.011 xi bn ≤ 0.001145672965 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13164 : ℝ) * (1 - 0.011))) ≤ 0.000566526496 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330070610 / (13164 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566526496 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566526496 : ℝ) + 3.141593 * 0.052298913366 / (13164 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145672965 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298913366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330070610) : PiBarMP 13164 12 0.011 xi bn ≤ 0.158355633775 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13164 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036470133123 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.101691486147 : ℝ) ≤ √((13164 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.734476074107 : ℝ) ≤ √(13164 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13164) ≤ 0.121431750417 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036470133123 + 0.052298913366 * 1.772454 / (2 * (114.101691486147 : ℝ))) * (1 + 0.001145672965) +
        8 / (13164 * 114.734476074107) + 0.121431750417 := by gcongr
    _ ≤ (0.158355633775 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298913366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330070610) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280230657696) :
    parallelOracle 13164 0.011 xi bn cd ≤ 0.159311182198 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13164 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13164 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523812131 : ℝ) ≤ plow 13164 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.734476074107 : ℝ) ≤ √(13164 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280230657696 : ℝ) / (2 * 0.560523812131 * 114.734476074107)) * 0.158355633775 +
        0.280230657696 ^ 2 / (2 * 0.560523812131 * 114.734476074107) := by gcongr
    _ ≤ (0.159311182198 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298913366) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330070610)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280230657696) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13164 13164 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523812131 : ℝ) ≤ plow 13164 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.734476074107 : ℝ) ≤ √(13164 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13164 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13164 Θ 1.22 ≤ 0.011557994994 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.734476074107 := by gcongr <;> linarith
      _ ≤ (0.011557994994 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13164 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13164 13164 0.011 ≤ 0.008331296157 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13164 13164 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13164 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13164 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13164 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13164 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159311182198 + 0.011557994994 + (0.008331296157 : ℝ) *
        (1 + 2 * (0.280230657696 + 0.011557994994) / (0.560523812131 * 114.734476074107))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13164]

end BstLean.Part269.N13164

/-! The original eight local profiles supply actual 13164 moment certificates. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13164 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052298913366 ∧
    0 ≤ bN 13164 BstLean.Part154.csC (groupTheta g) ∧ bN 13164 BstLean.Part154.csC (groupTheta g) ≤ 0.001330070610 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13164 13164 0.011
      (momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13164 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13164 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13164 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228689556749 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13164 0.011
      (momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13164 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13164
/-! The actual computed-centre upper energy formula at 13164. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13164

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13164)
open BstLean.Part268 (cell13164)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084241000885
  | 2 => 0.085164364145
  | 3 => 0.086083160224
  | 4 => 0.086998169586
  | 5 => 0.087910354177
  | 6 => 0.088820886547
  | 7 => 0.089731182138
  | 8 => 0.090642934847
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13164 13164 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13164 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13164

/-! Actual upper energy certificates on all 43 source endpoints at 13164. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13164)
open BstLean.Part268 (cell13164)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13164 (gMinus 13164) (1 - (cell13164 i).lower) ≤ 1 ∧
    energyUpper 13164 (gMinus 13164) (BstLean.Part211.gPlus 13164)
      (finiteEnergy 13164 13164 0.011) (1 - (cell13164 i).lower) ≤
      (cell13164 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨10,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨11,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨12,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨13,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨14,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨15,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨16,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨17,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨18,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨19,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨20,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨21,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨22,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨23,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨24,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨25,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨26,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨27,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨28,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨29,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨30,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨31,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨32,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨33,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨34,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨35,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨36,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨37,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨38,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨39,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨40,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨41,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨42,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨43,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨44,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨45,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨46,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨47,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨48,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨49,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨50,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨51,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13164) (by norm_num)
        (q := 1 - (cell13164 ⟨52,by decide⟩).lower)
        (by norm_num [cell13164]) (by norm_num [cell13164])
      exact ⟨E.1,E.2.trans (by norm_num [cell13164])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13164

/-! Source-cell containment and simple scalar guards at 13164. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13164)
open BstLean.Part268 (cell13164)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13164 ⟨10,by decide⟩).lower ∧ (cell13164 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13164 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13164 ⟨11,by decide⟩).lower ∧ (cell13164 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13164 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13164 ⟨12,by decide⟩).lower ∧ (cell13164 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13164 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13164 ⟨13,by decide⟩).lower ∧ (cell13164 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13164 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13164 ⟨14,by decide⟩).lower ∧ (cell13164 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13164 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13164 ⟨15,by decide⟩).lower ∧ (cell13164 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13164 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13164 ⟨16,by decide⟩).lower ∧ (cell13164 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13164 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13164 ⟨17,by decide⟩).lower ∧ (cell13164 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13164 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13164 ⟨18,by decide⟩).lower ∧ (cell13164 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13164 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13164 ⟨19,by decide⟩).lower ∧ (cell13164 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13164 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13164 ⟨20,by decide⟩).lower ∧ (cell13164 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13164 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13164 ⟨21,by decide⟩).lower ∧ (cell13164 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13164 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13164 ⟨22,by decide⟩).lower ∧ (cell13164 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13164 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13164 ⟨23,by decide⟩).lower ∧ (cell13164 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13164 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13164 ⟨24,by decide⟩).lower ∧ (cell13164 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13164 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13164 ⟨25,by decide⟩).lower ∧ (cell13164 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13164 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13164 ⟨26,by decide⟩).lower ∧ (cell13164 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13164 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13164 ⟨27,by decide⟩).lower ∧ (cell13164 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13164 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13164 ⟨28,by decide⟩).lower ∧ (cell13164 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13164 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13164 ⟨29,by decide⟩).lower ∧ (cell13164 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13164 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13164 ⟨30,by decide⟩).lower ∧ (cell13164 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13164 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13164 ⟨31,by decide⟩).lower ∧ (cell13164 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13164 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13164 ⟨32,by decide⟩).lower ∧ (cell13164 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13164 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13164 ⟨33,by decide⟩).lower ∧ (cell13164 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13164 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13164 ⟨34,by decide⟩).lower ∧ (cell13164 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13164 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13164 ⟨35,by decide⟩).lower ∧ (cell13164 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13164 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13164 ⟨36,by decide⟩).lower ∧ (cell13164 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13164 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13164 ⟨37,by decide⟩).lower ∧ (cell13164 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13164 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13164 ⟨38,by decide⟩).lower ∧ (cell13164 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13164 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13164 ⟨39,by decide⟩).lower ∧ (cell13164 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13164 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13164 ⟨40,by decide⟩).lower ∧ (cell13164 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13164 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13164 ⟨41,by decide⟩).lower ∧ (cell13164 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13164 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13164 ⟨42,by decide⟩).lower ∧ (cell13164 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13164 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13164 ⟨43,by decide⟩).lower ∧ (cell13164 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13164 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13164 ⟨44,by decide⟩).lower ∧ (cell13164 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13164 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13164 ⟨45,by decide⟩).lower ∧ (cell13164 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13164 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13164 ⟨46,by decide⟩).lower ∧ (cell13164 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13164 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13164 ⟨47,by decide⟩).lower ∧ (cell13164 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13164 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13164 ⟨48,by decide⟩).lower ∧ (cell13164 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13164 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13164 ⟨49,by decide⟩).lower ∧ (cell13164 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13164 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13164 ⟨50,by decide⟩).lower ∧ (cell13164 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13164 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13164 ⟨51,by decide⟩).lower ∧ (cell13164 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13164 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13164 ⟨52,by decide⟩).lower ∧ (cell13164 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13164 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13164 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13164 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13164,cell13164,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13164 i).lower ∧
    (cell13164 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13164 i).upper ≤ (0.532 : ℝ) ∧
    (cell13164 i).centre ≤ (0.1 : ℝ) ∧ (cell13164 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13164 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13164 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13164

/-! The local source numeric instances at 13164 have no network premises. -/
namespace BstLean.Part269.N13164
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13164)
open BstLean.Part268 (cell13164)

noncomputable def sourceNumerics13164 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13164 (cell13164 i)
      scalarRow13164.M scalarRow13164.H scalarRow13164.xi := by
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
    energy_allowance := scalarRow13164.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13164]
    centre_nonneg := (scalarRow13164.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13164])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13164
/-! Actual 13165 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13165 ≤ (1.035165616067 : ℝ) := by
  have hr : (114.738833879380 : ℝ) ≤ √(13165 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.738833879380 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13165 13165 (11 / 1000) ≤
    (0.008330979730 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13165) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.738833879380 : ℝ) ≤ √(13165 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13165)
  have hdiv : K / √(13165 : ℝ) ≤ K / 114.738833879380 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.738833879380 ≤ (0.008330979730 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13165.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13165 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13165 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13165 := gPlus_lower 13165
end BstLean.Part269.N13165

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13165
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035165616066 : ℝ) ≤ wn 13165 := by
  have hn : √(13165 : ℝ) ≤ 114.738833879381 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13165 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.738833879381 ≤ 2 / √(13165 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242833224 : ℝ) ≤ rhoBar 13165 BstLean.Part154.csC ∧
    rhoBar 13165 BstLean.Part154.csC ≤ 0.000242833600 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035165616066 : ℝ) / (1.295212 * 13165) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035165616067 : ℝ) / (1.29521 * 13165) := by gcongr
      _ ≤ (0.000242833600 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13165 BstLean.Part154.csC) ≤ 0.000971393369 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13165 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) ≤ 0.000185477632 ∧
    cc1 (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) ≤ 0.000118020713 ∧
    cc2 (rhoBar 13165 BstLean.Part154.csC) ≤ 0.000068512005 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13165 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13165 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13165 BstLean.Part154.csC * nuR (rhoBar 13165 BstLean.Part154.csC)) ≤ 0.000485681943 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242833600 : ℝ) * 0.000971393369 := by gcongr
      _ ≤ (0.000485681943 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13165 BstLean.Part154.csC) * nuR (rhoBar 13165 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971393369 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13165 BstLean.Part154.csC) * rhoBar 13165 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242833600 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242833600 / 2 + 0.399 * 0.000971393369 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185477632 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485681943 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118020713 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242833600 / 1.414213562 := by gcongr
      _ ≤ (0.000068512005 : ℝ) := by norm_num

end BstLean.Part269.N13165

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13165
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) ≤ 1.48566E-7 := by
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13165 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13165 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13165 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185477632 : ℝ) ^ 2 + 0.000118020713 ^ 2 + 3 * 0.000068512005 ^ 2 +
        2 * 0.797885 * 0.000185477632 * 0.000118020713 + 2 * 0.000185477632 * 0.000068512005 +
        4 * 0.797885 * 0.000118020713 * 0.000068512005 := by gcongr
    _ ≤ (1.48566E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13165 BstLean.Part154.csC Θ ≤ 0.002533268099 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13165 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13165 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13165 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035165616067 * 1.48566E-7 / (0.000242833224 : ℝ) := by gcongr
    _ ≤ 0.002533268099 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13165 BstLean.Part154.csC Θ ≤ 0.002809045814 + 0.000640116204 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13165 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13165 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035165616067 : ℝ) * ((2 * Θ * 0.000242833600 +
        (6863 / 10000) * 0.000242833600 * 13165 * 0.000971393369) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002809045814 + 0.000640116204 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13165 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13165 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13165 0.011 Θ ∧ gammaRatio 13165 0.011 Θ ≤ 0.000083479912 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13165 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035165616067 : ℝ) * 0.525 / ((1 - 0.011) * 13165) := by gcongr
      _ ≤ (0.000083479912 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13165 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13165 0.011 Θ) :=
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
    badAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13165 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13165 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13165 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13165 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13165 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13165 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13165 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13165 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13165 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13165 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035165616067 : ℝ) * 13165 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003125930972 + 0.003173384303 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13165

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13165
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13165 BstLean.Part154.csC) (piBar (rhoBar 13165 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13165 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13165 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13165 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13165 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13165 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13165 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13165 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13165 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13165 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13165 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051539122553 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13165) ≤ 0.010408311996 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13165 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035165616067)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010408311996 + 2 * 0.737676 / 13165) := by gcongr
    _ ≤ (0.051539122553 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13165 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13165

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13165
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523854219 : ℝ) ≤ plow 13165 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13165) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298557732)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329965752) : eMP 13165 0.011 xi bn ≤ 0.001145584227 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13165 : ℝ) * (1 - 0.011))) ≤ 0.000566482649 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329965752 / (13165 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566482649 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566482649 : ℝ) + 3.141593 * 0.052298557732 / (13165 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145584227 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298557732)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329965752) : PiBarMP 13165 12 0.011 xi bn ≤ 0.158349560422 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13165 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036468695508 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.106025257214 : ℝ) ≤ √((13165 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.738833879380 : ℝ) ≤ √(13165 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13165) ≤ 0.121427138413 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036468695508 + 0.052298557732 * 1.772454 / (2 * (114.106025257214 : ℝ))) * (1 + 0.001145584227) +
        8 / (13165 * 114.738833879380) + 0.121427138413 := by gcongr
    _ ≤ (0.158349560422 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298557732)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329965752) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280227901754) :
    parallelOracle 13165 0.011 xi bn cd ≤ 0.159305043849 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13165 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13165 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523854219 : ℝ) ≤ plow 13165 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.738833879380 : ℝ) ≤ √(13165 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280227901754 : ℝ) / (2 * 0.560523854219 * 114.738833879380)) * 0.158349560422 +
        0.280227901754 ^ 2 / (2 * 0.560523854219 * 114.738833879380) := by gcongr
    _ ≤ (0.159305043849 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298557732) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329965752)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280227901754) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13165 13165 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523854219 : ℝ) ≤ plow 13165 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.738833879380 : ℝ) ≤ √(13165 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13165 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13165 Θ 1.22 ≤ 0.011557556018 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.738833879380 := by gcongr <;> linarith
      _ ≤ (0.011557556018 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13165 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13165 13165 0.011 ≤ 0.008330979730 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13165 13165 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13165 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13165 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13165 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13165 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159305043849 + 0.011557556018 + (0.008330979730 : ℝ) *
        (1 + 2 * (0.280227901754 + 0.011557556018) / (0.560523854219 * 114.738833879380))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13165]

end BstLean.Part269.N13165

/-! The original eight local profiles supply actual 13165 moment certificates. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13165 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052298557732 ∧
    0 ≤ bN 13165 BstLean.Part154.csC (groupTheta g) ∧ bN 13165 BstLean.Part154.csC (groupTheta g) ≤ 0.001329965752 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13165 13165 0.011
      (momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13165 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13165 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13165 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228688779201 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13165 0.011
      (momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13165 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13165
/-! The actual computed-centre upper energy formula at 13165. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13165

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13165)
open BstLean.Part268 (cell13165)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084238505683
  | 2 => 0.085161838611
  | 3 => 0.086080600120
  | 4 => 0.086995569655
  | 5 => 0.087907707956
  | 6 => 0.088818186148
  | 7 => 0.089728418008
  | 8 => 0.090640095490
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13165 13165 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13165 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13165

/-! Actual upper energy certificates on all 43 source endpoints at 13165. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13165)
open BstLean.Part268 (cell13165)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13165 (gMinus 13165) (1 - (cell13165 i).lower) ≤ 1 ∧
    energyUpper 13165 (gMinus 13165) (BstLean.Part211.gPlus 13165)
      (finiteEnergy 13165 13165 0.011) (1 - (cell13165 i).lower) ≤
      (cell13165 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨10,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨11,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨12,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨13,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨14,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨15,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨16,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨17,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨18,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨19,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨20,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨21,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨22,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨23,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨24,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨25,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨26,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨27,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨28,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨29,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨30,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨31,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨32,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨33,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨34,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨35,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨36,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨37,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨38,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨39,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨40,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨41,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨42,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨43,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨44,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨45,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨46,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨47,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨48,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨49,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨50,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨51,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13165) (by norm_num)
        (q := 1 - (cell13165 ⟨52,by decide⟩).lower)
        (by norm_num [cell13165]) (by norm_num [cell13165])
      exact ⟨E.1,E.2.trans (by norm_num [cell13165])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13165

/-! Source-cell containment and simple scalar guards at 13165. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13165)
open BstLean.Part268 (cell13165)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13165 ⟨10,by decide⟩).lower ∧ (cell13165 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13165 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13165 ⟨11,by decide⟩).lower ∧ (cell13165 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13165 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13165 ⟨12,by decide⟩).lower ∧ (cell13165 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13165 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13165 ⟨13,by decide⟩).lower ∧ (cell13165 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13165 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13165 ⟨14,by decide⟩).lower ∧ (cell13165 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13165 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13165 ⟨15,by decide⟩).lower ∧ (cell13165 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13165 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13165 ⟨16,by decide⟩).lower ∧ (cell13165 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13165 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13165 ⟨17,by decide⟩).lower ∧ (cell13165 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13165 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13165 ⟨18,by decide⟩).lower ∧ (cell13165 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13165 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13165 ⟨19,by decide⟩).lower ∧ (cell13165 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13165 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13165 ⟨20,by decide⟩).lower ∧ (cell13165 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13165 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13165 ⟨21,by decide⟩).lower ∧ (cell13165 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13165 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13165 ⟨22,by decide⟩).lower ∧ (cell13165 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13165 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13165 ⟨23,by decide⟩).lower ∧ (cell13165 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13165 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13165 ⟨24,by decide⟩).lower ∧ (cell13165 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13165 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13165 ⟨25,by decide⟩).lower ∧ (cell13165 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13165 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13165 ⟨26,by decide⟩).lower ∧ (cell13165 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13165 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13165 ⟨27,by decide⟩).lower ∧ (cell13165 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13165 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13165 ⟨28,by decide⟩).lower ∧ (cell13165 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13165 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13165 ⟨29,by decide⟩).lower ∧ (cell13165 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13165 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13165 ⟨30,by decide⟩).lower ∧ (cell13165 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13165 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13165 ⟨31,by decide⟩).lower ∧ (cell13165 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13165 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13165 ⟨32,by decide⟩).lower ∧ (cell13165 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13165 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13165 ⟨33,by decide⟩).lower ∧ (cell13165 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13165 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13165 ⟨34,by decide⟩).lower ∧ (cell13165 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13165 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13165 ⟨35,by decide⟩).lower ∧ (cell13165 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13165 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13165 ⟨36,by decide⟩).lower ∧ (cell13165 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13165 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13165 ⟨37,by decide⟩).lower ∧ (cell13165 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13165 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13165 ⟨38,by decide⟩).lower ∧ (cell13165 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13165 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13165 ⟨39,by decide⟩).lower ∧ (cell13165 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13165 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13165 ⟨40,by decide⟩).lower ∧ (cell13165 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13165 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13165 ⟨41,by decide⟩).lower ∧ (cell13165 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13165 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13165 ⟨42,by decide⟩).lower ∧ (cell13165 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13165 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13165 ⟨43,by decide⟩).lower ∧ (cell13165 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13165 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13165 ⟨44,by decide⟩).lower ∧ (cell13165 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13165 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13165 ⟨45,by decide⟩).lower ∧ (cell13165 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13165 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13165 ⟨46,by decide⟩).lower ∧ (cell13165 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13165 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13165 ⟨47,by decide⟩).lower ∧ (cell13165 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13165 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13165 ⟨48,by decide⟩).lower ∧ (cell13165 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13165 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13165 ⟨49,by decide⟩).lower ∧ (cell13165 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13165 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13165 ⟨50,by decide⟩).lower ∧ (cell13165 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13165 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13165 ⟨51,by decide⟩).lower ∧ (cell13165 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13165 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13165 ⟨52,by decide⟩).lower ∧ (cell13165 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13165 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13165 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13165 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13165,cell13165,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13165 i).lower ∧
    (cell13165 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13165 i).upper ≤ (0.532 : ℝ) ∧
    (cell13165 i).centre ≤ (0.1 : ℝ) ∧ (cell13165 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13165 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13165 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13165

/-! The local source numeric instances at 13165 have no network premises. -/
namespace BstLean.Part269.N13165
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13165)
open BstLean.Part268 (cell13165)

noncomputable def sourceNumerics13165 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13165 (cell13165 i)
      scalarRow13165.M scalarRow13165.H scalarRow13165.xi := by
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
    energy_allowance := scalarRow13165.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13165]
    centre_nonneg := (scalarRow13165.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13165])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13165
/-! Actual 13166 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13166 ≤ (1.035164269033 : ℝ) := by
  have hr : (114.743191519148 : ℝ) ≤ √(13166 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.743191519148 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13166 13166 (11 / 1000) ≤
    (0.008330663340 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13166) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.743191519148 : ℝ) ≤ √(13166 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13166)
  have hdiv : K / √(13166 : ℝ) ≤ K / 114.743191519148 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.743191519148 ≤ (0.008330663340 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13166.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13166 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13166 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13166 := gPlus_lower 13166
end BstLean.Part269.N13166

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13166
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035164269032 : ℝ) ≤ wn 13166 := by
  have hn : √(13166 : ℝ) ≤ 114.743191519149 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13166 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.743191519149 ≤ 2 / √(13166 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242814464 : ℝ) ≤ rhoBar 13166 BstLean.Part154.csC ∧
    rhoBar 13166 BstLean.Part154.csC ≤ 0.000242814840 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035164269032 : ℝ) / (1.295212 * 13166) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035164269033 : ℝ) / (1.29521 * 13166) := by gcongr
      _ ≤ (0.000242814840 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13166 BstLean.Part154.csC) ≤ 0.000971318320 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13166 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) ≤ 0.000185463302 ∧
    cc1 (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) ≤ 0.000118011595 ∧
    cc2 (rhoBar 13166 BstLean.Part154.csC) ≤ 0.000068506712 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13166 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13166 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13166 BstLean.Part154.csC * nuR (rhoBar 13166 BstLean.Part154.csC)) ≤ 0.000485644420 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242814840 : ℝ) * 0.000971318320 := by gcongr
      _ ≤ (0.000485644420 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13166 BstLean.Part154.csC) * nuR (rhoBar 13166 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971318320 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13166 BstLean.Part154.csC) * rhoBar 13166 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242814840 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242814840 / 2 + 0.399 * 0.000971318320 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185463302 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485644420 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118011595 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242814840 / 1.414213562 := by gcongr
      _ ≤ (0.000068506712 : ℝ) := by norm_num

end BstLean.Part269.N13166

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13166
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) ≤ 1.48543E-7 := by
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13166 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13166 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13166 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185463302 : ℝ) ^ 2 + 0.000118011595 ^ 2 + 3 * 0.000068506712 ^ 2 +
        2 * 0.797885 * 0.000185463302 * 0.000118011595 + 2 * 0.000185463302 * 0.000068506712 +
        4 * 0.797885 * 0.000118011595 * 0.000068506712 := by gcongr
    _ ≤ (1.48543E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13166 BstLean.Part154.csC Θ ≤ 0.002533068311 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13166 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13166 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13166 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035164269033 * 1.48543E-7 / (0.000242814464 : ℝ) := by gcongr
    _ ≤ 0.002533068311 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13166 BstLean.Part154.csC Θ ≤ 0.002808821479 + 0.000640065920 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13166 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13166 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035164269033 : ℝ) * ((2 * Θ * 0.000242814840 +
        (6863 / 10000) * 0.000242814840 * 13166 * 0.000971318320) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002808821479 + 0.000640065920 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13166 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13166 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13166 0.011 Θ ∧ gammaRatio 13166 0.011 Θ ≤ 0.000083473463 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13166 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035164269033 : ℝ) * 0.525 / ((1 - 0.011) * 13166) := by gcongr
      _ ≤ (0.000083473463 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13166 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13166 0.011 Θ) :=
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
    badAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13166 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13166 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13166 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13166 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13166 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13166 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13166 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13166 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13166 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13166 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035164269033 : ℝ) * 13166 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003125706637 + 0.003173134231 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13166

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13166
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13166 BstLean.Part154.csC) (piBar (rhoBar 13166 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13166 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13166 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13166 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13166 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13166 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13166 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13166 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13166 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13166 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13166 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051537144385 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13166) ≤ 0.010407916716 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13166 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035164269033)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010407916716 + 2 * 0.737676 / 13166) := by gcongr
    _ ≤ (0.051537144385 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13166 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13166

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13166
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523896301 : ℝ) ≤ plow 13166 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13166) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298202109)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329860864) : eMP 13166 0.011 xi bn ≤ 0.001145495481 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13166 : ℝ) * (1 - 0.011))) ≤ 0.000566438798 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329860864 / (13166 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566438798 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566438798 : ℝ) + 3.141593 * 0.052298202109 / (13166 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145495481 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298202109)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329860864) : PiBarMP 13166 12 0.011 xi bn ≤ 0.158343487128 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13166 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036467257424 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.110358863689 : ℝ) ≤ √((13166 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.743191519148 : ℝ) ≤ √(13166 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13166) ≤ 0.121422526935 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036467257424 + 0.052298202109 * 1.772454 / (2 * (114.110358863689 : ℝ))) * (1 + 0.001145495481) +
        8 / (13166 * 114.743191519148) + 0.121422526935 := by gcongr
    _ ≤ (0.158343487128 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298202109)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329860864) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280225146058) :
    parallelOracle 13166 0.011 xi bn cd ≤ 0.159298905567 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13166 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13166 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523896301 : ℝ) ≤ plow 13166 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.743191519148 : ℝ) ≤ √(13166 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280225146058 : ℝ) / (2 * 0.560523896301 * 114.743191519148)) * 0.158343487128 +
        0.280225146058 ^ 2 / (2 * 0.560523896301 * 114.743191519148) := by gcongr
    _ ≤ (0.159298905567 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052298202109) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329860864)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280225146058) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13166 13166 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523896301 : ℝ) ≤ plow 13166 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.743191519148 : ℝ) ≤ √(13166 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13166 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13166 Θ 1.22 ≤ 0.011557117093 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.743191519148 := by gcongr <;> linarith
      _ ≤ (0.011557117093 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13166 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13166 13166 0.011 ≤ 0.008330663340 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13166 13166 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13166 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13166 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13166 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13166 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159298905567 + 0.011557117093 + (0.008330663340 : ℝ) *
        (1 + 2 * (0.280225146058 + 0.011557117093) / (0.560523896301 * 114.743191519148))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13166]

end BstLean.Part269.N13166

/-! The original eight local profiles supply actual 13166 moment certificates. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13166 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052298202109 ∧
    0 ≤ bN 13166 BstLean.Part154.csC (groupTheta g) ∧ bN 13166 BstLean.Part154.csC (groupTheta g) ≤ 0.001329860864 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13166 13166 0.011
      (momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13166 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13166 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13166 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228688001673 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13166 0.011
      (momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13166 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13166
/-! The actual computed-centre upper energy formula at 13166. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13166

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13166)
open BstLean.Part268 (cell13166)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084236011178
  | 2 => 0.085159313797
  | 3 => 0.086078040764
  | 4 => 0.086992970508
  | 5 => 0.087905062562
  | 6 => 0.088815486631
  | 7 => 0.089725654824
  | 8 => 0.090637257157
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13166 13166 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13166 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13166

/-! Actual upper energy certificates on all 43 source endpoints at 13166. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13166)
open BstLean.Part268 (cell13166)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13166 (gMinus 13166) (1 - (cell13166 i).lower) ≤ 1 ∧
    energyUpper 13166 (gMinus 13166) (BstLean.Part211.gPlus 13166)
      (finiteEnergy 13166 13166 0.011) (1 - (cell13166 i).lower) ≤
      (cell13166 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨10,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨11,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨12,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨13,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨14,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨15,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨16,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨17,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨18,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨19,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨20,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨21,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨22,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨23,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨24,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨25,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨26,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨27,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨28,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨29,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨30,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨31,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨32,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨33,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨34,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨35,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨36,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨37,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨38,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨39,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨40,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨41,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨42,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨43,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨44,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨45,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨46,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨47,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨48,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨49,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨50,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨51,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13166) (by norm_num)
        (q := 1 - (cell13166 ⟨52,by decide⟩).lower)
        (by norm_num [cell13166]) (by norm_num [cell13166])
      exact ⟨E.1,E.2.trans (by norm_num [cell13166])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13166

/-! Source-cell containment and simple scalar guards at 13166. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13166)
open BstLean.Part268 (cell13166)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13166 ⟨10,by decide⟩).lower ∧ (cell13166 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13166 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13166 ⟨11,by decide⟩).lower ∧ (cell13166 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13166 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13166 ⟨12,by decide⟩).lower ∧ (cell13166 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13166 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13166 ⟨13,by decide⟩).lower ∧ (cell13166 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13166 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13166 ⟨14,by decide⟩).lower ∧ (cell13166 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13166 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13166 ⟨15,by decide⟩).lower ∧ (cell13166 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13166 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13166 ⟨16,by decide⟩).lower ∧ (cell13166 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13166 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13166 ⟨17,by decide⟩).lower ∧ (cell13166 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13166 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13166 ⟨18,by decide⟩).lower ∧ (cell13166 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13166 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13166 ⟨19,by decide⟩).lower ∧ (cell13166 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13166 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13166 ⟨20,by decide⟩).lower ∧ (cell13166 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13166 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13166 ⟨21,by decide⟩).lower ∧ (cell13166 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13166 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13166 ⟨22,by decide⟩).lower ∧ (cell13166 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13166 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13166 ⟨23,by decide⟩).lower ∧ (cell13166 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13166 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13166 ⟨24,by decide⟩).lower ∧ (cell13166 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13166 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13166 ⟨25,by decide⟩).lower ∧ (cell13166 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13166 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13166 ⟨26,by decide⟩).lower ∧ (cell13166 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13166 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13166 ⟨27,by decide⟩).lower ∧ (cell13166 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13166 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13166 ⟨28,by decide⟩).lower ∧ (cell13166 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13166 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13166 ⟨29,by decide⟩).lower ∧ (cell13166 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13166 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13166 ⟨30,by decide⟩).lower ∧ (cell13166 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13166 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13166 ⟨31,by decide⟩).lower ∧ (cell13166 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13166 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13166 ⟨32,by decide⟩).lower ∧ (cell13166 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13166 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13166 ⟨33,by decide⟩).lower ∧ (cell13166 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13166 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13166 ⟨34,by decide⟩).lower ∧ (cell13166 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13166 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13166 ⟨35,by decide⟩).lower ∧ (cell13166 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13166 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13166 ⟨36,by decide⟩).lower ∧ (cell13166 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13166 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13166 ⟨37,by decide⟩).lower ∧ (cell13166 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13166 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13166 ⟨38,by decide⟩).lower ∧ (cell13166 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13166 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13166 ⟨39,by decide⟩).lower ∧ (cell13166 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13166 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13166 ⟨40,by decide⟩).lower ∧ (cell13166 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13166 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13166 ⟨41,by decide⟩).lower ∧ (cell13166 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13166 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13166 ⟨42,by decide⟩).lower ∧ (cell13166 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13166 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13166 ⟨43,by decide⟩).lower ∧ (cell13166 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13166 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13166 ⟨44,by decide⟩).lower ∧ (cell13166 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13166 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13166 ⟨45,by decide⟩).lower ∧ (cell13166 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13166 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13166 ⟨46,by decide⟩).lower ∧ (cell13166 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13166 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13166 ⟨47,by decide⟩).lower ∧ (cell13166 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13166 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13166 ⟨48,by decide⟩).lower ∧ (cell13166 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13166 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13166 ⟨49,by decide⟩).lower ∧ (cell13166 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13166 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13166 ⟨50,by decide⟩).lower ∧ (cell13166 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13166 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13166 ⟨51,by decide⟩).lower ∧ (cell13166 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13166 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13166 ⟨52,by decide⟩).lower ∧ (cell13166 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13166 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13166 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13166 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13166,cell13166,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13166 i).lower ∧
    (cell13166 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13166 i).upper ≤ (0.532 : ℝ) ∧
    (cell13166 i).centre ≤ (0.1 : ℝ) ∧ (cell13166 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13166 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13166 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13166

/-! The local source numeric instances at 13166 have no network premises. -/
namespace BstLean.Part269.N13166
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13166)
open BstLean.Part268 (cell13166)

noncomputable def sourceNumerics13166 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13166 (cell13166 i)
      scalarRow13166.M scalarRow13166.H scalarRow13166.xi := by
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
    energy_allowance := scalarRow13166.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13166]
    centre_nonneg := (scalarRow13166.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13166])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13166
/-! Actual 13167 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13167 ≤ (1.035162922152 : ℝ) := by
  have hr : (114.747548993431 : ℝ) ≤ √(13167 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.747548993431 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13167 13167 (11 / 1000) ≤
    (0.008330346985 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13167) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.747548993431 : ℝ) ≤ √(13167 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13167)
  have hdiv : K / √(13167 : ℝ) ≤ K / 114.747548993431 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.747548993431 ≤ (0.008330346985 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13167.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13167 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13167 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13167 := gPlus_lower 13167
end BstLean.Part269.N13167

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13167
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035162922151 : ℝ) ≤ wn 13167 := by
  have hn : √(13167 : ℝ) ≤ 114.747548993432 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13167 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.747548993432 ≤ 2 / √(13167 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242795707 : ℝ) ≤ rhoBar 13167 BstLean.Part154.csC ∧
    rhoBar 13167 BstLean.Part154.csC ≤ 0.000242796083 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035162922151 : ℝ) / (1.295212 * 13167) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035162922152 : ℝ) / (1.29521 * 13167) := by gcongr
      _ ≤ (0.000242796083 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13167 BstLean.Part154.csC) ≤ 0.000971243282 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13167 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) ≤ 0.000185448975 ∧
    cc1 (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) ≤ 0.000118002478 ∧
    cc2 (rhoBar 13167 BstLean.Part154.csC) ≤ 0.000068501420 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13167 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13167 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13167 BstLean.Part154.csC * nuR (rhoBar 13167 BstLean.Part154.csC)) ≤ 0.000485606904 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242796083 : ℝ) * 0.000971243282 := by gcongr
      _ ≤ (0.000485606904 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13167 BstLean.Part154.csC) * nuR (rhoBar 13167 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971243282 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13167 BstLean.Part154.csC) * rhoBar 13167 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242796083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242796083 / 2 + 0.399 * 0.000971243282 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185448975 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485606904 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118002478 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242796083 / 1.414213562 := by gcongr
      _ ≤ (0.000068501420 : ℝ) := by norm_num

end BstLean.Part269.N13167

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13167
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) ≤ 1.48520E-7 := by
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13167 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13167 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13167 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185448975 : ℝ) ^ 2 + 0.000118002478 ^ 2 + 3 * 0.000068501420 ^ 2 +
        2 * 0.797885 * 0.000185448975 * 0.000118002478 + 2 * 0.000185448975 * 0.000068501420 +
        4 * 0.797885 * 0.000118002478 * 0.000068501420 := by gcongr
    _ ≤ (1.48520E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13167 BstLean.Part154.csC Θ ≤ 0.002532868462 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13167 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13167 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13167 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035162922152 * 1.48520E-7 / (0.000242795707 : ℝ) := by gcongr
    _ ≤ 0.002532868462 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13167 BstLean.Part154.csC Θ ≤ 0.002808597179 + 0.000640015643 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13167 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13167 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035162922152 : ℝ) * ((2 * Θ * 0.000242796083 +
        (6863 / 10000) * 0.000242796083 * 13167 * 0.000971243282) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002808597179 + 0.000640015643 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13167 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13167 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13167 0.011 Θ ∧ gammaRatio 13167 0.011 Θ ≤ 0.000083467015 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13167 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035162922152 : ℝ) * 0.525 / ((1 - 0.011) * 13167) := by gcongr
      _ ≤ (0.000083467015 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13167 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13167 0.011 Θ) :=
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
    badAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13167 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13167 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13167 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13167 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13167 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13167 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13167 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13167 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13167 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13167 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035162922152 : ℝ) * 13167 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003125482337 + 0.003172884105 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13167

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13167
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13167 BstLean.Part154.csC) (piBar (rhoBar 13167 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13167 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13167 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13167 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13167 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13167 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13167 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13167 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13167 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13167 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13167 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051535166449 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13167) ≤ 0.010407521482 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13167 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035162922152)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010407521482 + 2 * 0.737676 / 13167) := by gcongr
    _ ≤ (0.051535166449 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13167 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13167

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13167
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523938376 : ℝ) ≤ plow 13167 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13167) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297846493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329755943) : eMP 13167 0.011 xi bn ≤ 0.001145406727 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13167 : ℝ) * (1 - 0.011))) ≤ 0.000566394943 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329755943 / (13167 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566394943 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566394943 : ℝ) + 3.141593 * 0.052297846493 / (13167 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145406727 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297846493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329755943) : PiBarMP 13167 12 0.011 xi bn ≤ 0.158337413852 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13167 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036465818831 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.114692305592 : ℝ) ≤ √((13167 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.747548993431 : ℝ) ≤ √(13167 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13167) ≤ 0.121417915982 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036465818831 + 0.052297846493 * 1.772454 / (2 * (114.114692305592 : ℝ))) * (1 + 0.001145406727) +
        8 / (13167 * 114.747548993431) + 0.121417915982 := by gcongr
    _ ≤ (0.158337413852 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297846493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329755943) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280222390607) :
    parallelOracle 13167 0.011 xi bn cd ≤ 0.159292767311 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13167 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13167 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523938376 : ℝ) ≤ plow 13167 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.747548993431 : ℝ) ≤ √(13167 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280222390607 : ℝ) / (2 * 0.560523938376 * 114.747548993431)) * 0.158337413852 +
        0.280222390607 ^ 2 / (2 * 0.560523938376 * 114.747548993431) := by gcongr
    _ ≤ (0.159292767311 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297846493) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329755943)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280222390607) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13167 13167 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523938376 : ℝ) ≤ plow 13167 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.747548993431 : ℝ) ≤ √(13167 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13167 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13167 Θ 1.22 ≤ 0.011556678218 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.747548993431 := by gcongr <;> linarith
      _ ≤ (0.011556678218 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13167 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13167 13167 0.011 ≤ 0.008330346985 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13167 13167 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13167 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13167 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13167 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13167 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159292767311 + 0.011556678218 + (0.008330346985 : ℝ) *
        (1 + 2 * (0.280222390607 + 0.011556678218) / (0.560523938376 * 114.747548993431))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13167]

end BstLean.Part269.N13167

/-! The original eight local profiles supply actual 13167 moment certificates. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13167 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052297846493 ∧
    0 ≤ bN 13167 BstLean.Part154.csC (groupTheta g) ∧ bN 13167 BstLean.Part154.csC (groupTheta g) ≤ 0.001329755943 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13167 13167 0.011
      (momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13167 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13167 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13167 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228687224158 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13167 0.011
      (momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13167 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13167
/-! The actual computed-centre upper energy formula at 13167. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13167

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13167)
open BstLean.Part268 (cell13167)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084233517369
  | 2 => 0.085156789702
  | 3 => 0.086075482155
  | 4 => 0.086990372144
  | 5 => 0.087902417995
  | 6 => 0.088812787993
  | 7 => 0.089722892584
  | 8 => 0.090634419847
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13167 13167 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13167 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13167

/-! Actual upper energy certificates on all 43 source endpoints at 13167. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13167)
open BstLean.Part268 (cell13167)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13167 (gMinus 13167) (1 - (cell13167 i).lower) ≤ 1 ∧
    energyUpper 13167 (gMinus 13167) (BstLean.Part211.gPlus 13167)
      (finiteEnergy 13167 13167 0.011) (1 - (cell13167 i).lower) ≤
      (cell13167 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨10,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨11,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨12,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨13,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨14,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨15,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨16,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨17,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨18,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨19,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨20,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨21,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨22,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨23,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨24,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨25,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨26,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨27,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨28,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨29,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨30,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨31,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨32,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨33,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨34,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨35,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨36,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨37,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨38,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨39,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨40,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨41,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨42,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨43,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨44,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨45,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨46,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨47,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨48,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨49,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨50,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨51,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13167) (by norm_num)
        (q := 1 - (cell13167 ⟨52,by decide⟩).lower)
        (by norm_num [cell13167]) (by norm_num [cell13167])
      exact ⟨E.1,E.2.trans (by norm_num [cell13167])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13167

/-! Source-cell containment and simple scalar guards at 13167. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13167)
open BstLean.Part268 (cell13167)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13167 ⟨10,by decide⟩).lower ∧ (cell13167 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13167 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13167 ⟨11,by decide⟩).lower ∧ (cell13167 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13167 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13167 ⟨12,by decide⟩).lower ∧ (cell13167 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13167 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13167 ⟨13,by decide⟩).lower ∧ (cell13167 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13167 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13167 ⟨14,by decide⟩).lower ∧ (cell13167 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13167 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13167 ⟨15,by decide⟩).lower ∧ (cell13167 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13167 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13167 ⟨16,by decide⟩).lower ∧ (cell13167 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13167 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13167 ⟨17,by decide⟩).lower ∧ (cell13167 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13167 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13167 ⟨18,by decide⟩).lower ∧ (cell13167 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13167 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13167 ⟨19,by decide⟩).lower ∧ (cell13167 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13167 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13167 ⟨20,by decide⟩).lower ∧ (cell13167 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13167 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13167 ⟨21,by decide⟩).lower ∧ (cell13167 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13167 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13167 ⟨22,by decide⟩).lower ∧ (cell13167 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13167 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13167 ⟨23,by decide⟩).lower ∧ (cell13167 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13167 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13167 ⟨24,by decide⟩).lower ∧ (cell13167 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13167 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13167 ⟨25,by decide⟩).lower ∧ (cell13167 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13167 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13167 ⟨26,by decide⟩).lower ∧ (cell13167 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13167 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13167 ⟨27,by decide⟩).lower ∧ (cell13167 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13167 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13167 ⟨28,by decide⟩).lower ∧ (cell13167 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13167 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13167 ⟨29,by decide⟩).lower ∧ (cell13167 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13167 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13167 ⟨30,by decide⟩).lower ∧ (cell13167 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13167 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13167 ⟨31,by decide⟩).lower ∧ (cell13167 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13167 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13167 ⟨32,by decide⟩).lower ∧ (cell13167 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13167 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13167 ⟨33,by decide⟩).lower ∧ (cell13167 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13167 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13167 ⟨34,by decide⟩).lower ∧ (cell13167 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13167 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13167 ⟨35,by decide⟩).lower ∧ (cell13167 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13167 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13167 ⟨36,by decide⟩).lower ∧ (cell13167 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13167 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13167 ⟨37,by decide⟩).lower ∧ (cell13167 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13167 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13167 ⟨38,by decide⟩).lower ∧ (cell13167 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13167 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13167 ⟨39,by decide⟩).lower ∧ (cell13167 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13167 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13167 ⟨40,by decide⟩).lower ∧ (cell13167 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13167 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13167 ⟨41,by decide⟩).lower ∧ (cell13167 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13167 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13167 ⟨42,by decide⟩).lower ∧ (cell13167 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13167 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13167 ⟨43,by decide⟩).lower ∧ (cell13167 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13167 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13167 ⟨44,by decide⟩).lower ∧ (cell13167 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13167 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13167 ⟨45,by decide⟩).lower ∧ (cell13167 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13167 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13167 ⟨46,by decide⟩).lower ∧ (cell13167 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13167 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13167 ⟨47,by decide⟩).lower ∧ (cell13167 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13167 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13167 ⟨48,by decide⟩).lower ∧ (cell13167 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13167 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13167 ⟨49,by decide⟩).lower ∧ (cell13167 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13167 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13167 ⟨50,by decide⟩).lower ∧ (cell13167 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13167 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13167 ⟨51,by decide⟩).lower ∧ (cell13167 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13167 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13167 ⟨52,by decide⟩).lower ∧ (cell13167 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13167 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13167 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13167 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13167,cell13167,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13167 i).lower ∧
    (cell13167 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13167 i).upper ≤ (0.532 : ℝ) ∧
    (cell13167 i).centre ≤ (0.1 : ℝ) ∧ (cell13167 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13167 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13167 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13167

/-! The local source numeric instances at 13167 have no network premises. -/
namespace BstLean.Part269.N13167
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13167)
open BstLean.Part268 (cell13167)

noncomputable def sourceNumerics13167 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13167 (cell13167 i)
      scalarRow13167.M scalarRow13167.H scalarRow13167.xi := by
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
    energy_allowance := scalarRow13167.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13167]
    centre_nonneg := (scalarRow13167.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13167])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13167
/-! Actual 13168 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13168 ≤ (1.035161575426 : ℝ) := by
  have hr : (114.751906302248 : ℝ) ≤ √(13168 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.751906302248 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13168 13168 (11 / 1000) ≤
    (0.008330030666 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13168) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.751906302248 : ℝ) ≤ √(13168 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13168)
  have hdiv : K / √(13168 : ℝ) ≤ K / 114.751906302248 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.751906302248 ≤ (0.008330030666 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13168.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13168 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13168 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13168 := gPlus_lower 13168
end BstLean.Part269.N13168

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13168
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035161575425 : ℝ) ≤ wn 13168 := by
  have hn : √(13168 : ℝ) ≤ 114.751906302249 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13168 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.751906302249 ≤ 2 / √(13168 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242776953 : ℝ) ≤ rhoBar 13168 BstLean.Part154.csC ∧
    rhoBar 13168 BstLean.Part154.csC ≤ 0.000242777329 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035161575425 : ℝ) / (1.295212 * 13168) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035161575426 : ℝ) / (1.29521 * 13168) := by gcongr
      _ ≤ (0.000242777329 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13168 BstLean.Part154.csC) ≤ 0.000971168257 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13168 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) ≤ 0.000185434650 ∧
    cc1 (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) ≤ 0.000117993363 ∧
    cc2 (rhoBar 13168 BstLean.Part154.csC) ≤ 0.000068496129 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13168 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13168 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13168 BstLean.Part154.csC * nuR (rhoBar 13168 BstLean.Part154.csC)) ≤ 0.000485569394 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242777329 : ℝ) * 0.000971168257 := by gcongr
      _ ≤ (0.000485569394 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13168 BstLean.Part154.csC) * nuR (rhoBar 13168 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971168257 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13168 BstLean.Part154.csC) * rhoBar 13168 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242777329 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242777329 / 2 + 0.399 * 0.000971168257 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185434650 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485569394 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117993363 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242777329 / 1.414213562 := by gcongr
      _ ≤ (0.000068496129 : ℝ) := by norm_num

end BstLean.Part269.N13168

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13168
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) ≤ 1.48497E-7 := by
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13168 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13168 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13168 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185434650 : ℝ) ^ 2 + 0.000117993363 ^ 2 + 3 * 0.000068496129 ^ 2 +
        2 * 0.797885 * 0.000185434650 * 0.000117993363 + 2 * 0.000185434650 * 0.000068496129 +
        4 * 0.797885 * 0.000117993363 * 0.000068496129 := by gcongr
    _ ≤ (1.48497E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13168 BstLean.Part154.csC Θ ≤ 0.002532668552 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13168 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13168 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13168 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035161575426 * 1.48497E-7 / (0.000242776953 : ℝ) := by gcongr
    _ ≤ 0.002532668552 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13168 BstLean.Part154.csC Θ ≤ 0.002808372920 + 0.000639965374 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13168 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13168 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035161575426 : ℝ) * ((2 * Θ * 0.000242777329 +
        (6863 / 10000) * 0.000242777329 * 13168 * 0.000971168257) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002808372920 + 0.000639965374 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13168 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13168 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13168 0.011 Θ ∧ gammaRatio 13168 0.011 Θ ≤ 0.000083460568 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13168 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035161575426 : ℝ) * 0.525 / ((1 - 0.011) * 13168) := by gcongr
      _ ≤ (0.000083460568 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13168 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13168 0.011 Θ) :=
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
    badAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13168 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13168 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13168 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13168 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13168 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13168 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13168 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13168 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13168 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13168 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035161575426 : ℝ) * 13168 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003125258078 + 0.003172633926 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13168

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13168
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13168 BstLean.Part154.csC) (piBar (rhoBar 13168 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13168 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13168 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13168 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13168 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13168 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13168 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13168 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13168 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13168 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13168 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051533188734 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13168) ≤ 0.010407126292 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13168 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035161575426)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010407126292 + 2 * 0.737676 / 13168) := by gcongr
    _ ≤ (0.051533188734 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13168 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13168

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13168
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523980445 : ℝ) ≤ plow 13168 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13168) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297490890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329650990) : eMP 13168 0.011 xi bn ≤ 0.001145317967 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13168 : ℝ) * (1 - 0.011))) ≤ 0.000566351085 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329650990 / (13168 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566351085 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566351085 : ℝ) + 3.141593 * 0.052297490890 / (13168 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145317967 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297490890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329650990) : PiBarMP 13168 12 0.011 xi bn ≤ 0.158331340607 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13168 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036464379743 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.119025582941 : ℝ) ≤ √((13168 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.751906302248 : ℝ) ≤ √(13168 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13168) ≤ 0.121413305554 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036464379743 + 0.052297490890 * 1.772454 / (2 * (114.119025582941 : ℝ))) * (1 + 0.001145317967) +
        8 / (13168 * 114.751906302248) + 0.121413305554 := by gcongr
    _ ≤ (0.158331340607 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297490890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329650990) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280219635403) :
    parallelOracle 13168 0.011 xi bn cd ≤ 0.159286629094 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13168 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13168 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523980445 : ℝ) ≤ plow 13168 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.751906302248 : ℝ) ≤ √(13168 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280219635403 : ℝ) / (2 * 0.560523980445 * 114.751906302248)) * 0.158331340607 +
        0.280219635403 ^ 2 / (2 * 0.560523980445 * 114.751906302248) := by gcongr
    _ ≤ (0.159286629094 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297490890) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329650990)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280219635403) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13168 13168 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523980445 : ℝ) ≤ plow 13168 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.751906302248 : ℝ) ≤ √(13168 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13168 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13168 Θ 1.22 ≤ 0.011556239393 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.751906302248 := by gcongr <;> linarith
      _ ≤ (0.011556239393 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13168 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13168 13168 0.011 ≤ 0.008330030666 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13168 13168 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13168 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13168 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13168 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13168 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159286629094 + 0.011556239393 + (0.008330030666 : ℝ) *
        (1 + 2 * (0.280219635403 + 0.011556239393) / (0.560523980445 * 114.751906302248))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13168]

end BstLean.Part269.N13168

/-! The original eight local profiles supply actual 13168 moment certificates. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13168 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052297490890 ∧
    0 ≤ bN 13168 BstLean.Part154.csC (groupTheta g) ∧ bN 13168 BstLean.Part154.csC (groupTheta g) ≤ 0.001329650990 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13168 13168 0.011
      (momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13168 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13168 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13168 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228686446669 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13168 0.011
      (momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13168 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13168
/-! The actual computed-centre upper energy formula at 13168. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13168

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13168)
open BstLean.Part268 (cell13168)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084231024255
  | 2 => 0.085154266325
  | 3 => 0.086072924294
  | 4 => 0.086987774562
  | 5 => 0.087899774253
  | 6 => 0.088810090233
  | 7 => 0.089720131287
  | 8 => 0.090631583558
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13168 13168 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13168 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13168

/-! Actual upper energy certificates on all 43 source endpoints at 13168. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13168)
open BstLean.Part268 (cell13168)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13168 (gMinus 13168) (1 - (cell13168 i).lower) ≤ 1 ∧
    energyUpper 13168 (gMinus 13168) (BstLean.Part211.gPlus 13168)
      (finiteEnergy 13168 13168 0.011) (1 - (cell13168 i).lower) ≤
      (cell13168 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨10,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨11,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨12,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨13,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨14,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨15,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨16,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨17,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨18,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨19,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨20,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨21,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨22,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨23,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨24,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨25,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨26,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨27,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨28,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨29,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨30,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨31,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨32,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨33,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨34,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨35,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨36,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨37,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨38,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨39,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨40,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨41,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨42,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨43,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨44,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨45,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨46,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨47,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨48,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨49,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨50,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨51,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13168) (by norm_num)
        (q := 1 - (cell13168 ⟨52,by decide⟩).lower)
        (by norm_num [cell13168]) (by norm_num [cell13168])
      exact ⟨E.1,E.2.trans (by norm_num [cell13168])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13168

/-! Source-cell containment and simple scalar guards at 13168. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13168)
open BstLean.Part268 (cell13168)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13168 ⟨10,by decide⟩).lower ∧ (cell13168 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13168 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13168 ⟨11,by decide⟩).lower ∧ (cell13168 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13168 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13168 ⟨12,by decide⟩).lower ∧ (cell13168 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13168 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13168 ⟨13,by decide⟩).lower ∧ (cell13168 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13168 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13168 ⟨14,by decide⟩).lower ∧ (cell13168 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13168 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13168 ⟨15,by decide⟩).lower ∧ (cell13168 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13168 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13168 ⟨16,by decide⟩).lower ∧ (cell13168 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13168 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13168 ⟨17,by decide⟩).lower ∧ (cell13168 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13168 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13168 ⟨18,by decide⟩).lower ∧ (cell13168 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13168 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13168 ⟨19,by decide⟩).lower ∧ (cell13168 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13168 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13168 ⟨20,by decide⟩).lower ∧ (cell13168 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13168 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13168 ⟨21,by decide⟩).lower ∧ (cell13168 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13168 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13168 ⟨22,by decide⟩).lower ∧ (cell13168 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13168 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13168 ⟨23,by decide⟩).lower ∧ (cell13168 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13168 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13168 ⟨24,by decide⟩).lower ∧ (cell13168 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13168 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13168 ⟨25,by decide⟩).lower ∧ (cell13168 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13168 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13168 ⟨26,by decide⟩).lower ∧ (cell13168 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13168 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13168 ⟨27,by decide⟩).lower ∧ (cell13168 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13168 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13168 ⟨28,by decide⟩).lower ∧ (cell13168 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13168 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13168 ⟨29,by decide⟩).lower ∧ (cell13168 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13168 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13168 ⟨30,by decide⟩).lower ∧ (cell13168 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13168 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13168 ⟨31,by decide⟩).lower ∧ (cell13168 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13168 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13168 ⟨32,by decide⟩).lower ∧ (cell13168 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13168 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13168 ⟨33,by decide⟩).lower ∧ (cell13168 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13168 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13168 ⟨34,by decide⟩).lower ∧ (cell13168 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13168 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13168 ⟨35,by decide⟩).lower ∧ (cell13168 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13168 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13168 ⟨36,by decide⟩).lower ∧ (cell13168 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13168 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13168 ⟨37,by decide⟩).lower ∧ (cell13168 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13168 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13168 ⟨38,by decide⟩).lower ∧ (cell13168 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13168 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13168 ⟨39,by decide⟩).lower ∧ (cell13168 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13168 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13168 ⟨40,by decide⟩).lower ∧ (cell13168 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13168 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13168 ⟨41,by decide⟩).lower ∧ (cell13168 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13168 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13168 ⟨42,by decide⟩).lower ∧ (cell13168 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13168 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13168 ⟨43,by decide⟩).lower ∧ (cell13168 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13168 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13168 ⟨44,by decide⟩).lower ∧ (cell13168 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13168 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13168 ⟨45,by decide⟩).lower ∧ (cell13168 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13168 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13168 ⟨46,by decide⟩).lower ∧ (cell13168 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13168 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13168 ⟨47,by decide⟩).lower ∧ (cell13168 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13168 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13168 ⟨48,by decide⟩).lower ∧ (cell13168 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13168 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13168 ⟨49,by decide⟩).lower ∧ (cell13168 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13168 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13168 ⟨50,by decide⟩).lower ∧ (cell13168 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13168 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13168 ⟨51,by decide⟩).lower ∧ (cell13168 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13168 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13168 ⟨52,by decide⟩).lower ∧ (cell13168 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13168 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13168 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13168 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13168,cell13168,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13168 i).lower ∧
    (cell13168 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13168 i).upper ≤ (0.532 : ℝ) ∧
    (cell13168 i).centre ≤ (0.1 : ℝ) ∧ (cell13168 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13168 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13168 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13168

/-! The local source numeric instances at 13168 have no network premises. -/
namespace BstLean.Part269.N13168
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13168)
open BstLean.Part268 (cell13168)

noncomputable def sourceNumerics13168 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13168 (cell13168 i)
      scalarRow13168.M scalarRow13168.H scalarRow13168.xi := by
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
    energy_allowance := scalarRow13168.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13168]
    centre_nonneg := (scalarRow13168.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13168])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13168
/-! Actual 13169 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13169 ≤ (1.035160228855 : ℝ) := by
  have hr : (114.756263445617 : ℝ) ≤ √(13169 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.756263445617 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13169 13169 (11 / 1000) ≤
    (0.008329714384 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13169) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.756263445617 : ℝ) ≤ √(13169 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13169)
  have hdiv : K / √(13169 : ℝ) ≤ K / 114.756263445617 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.756263445617 ≤ (0.008329714384 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13169.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13169 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13169 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13169 := gPlus_lower 13169
end BstLean.Part269.N13169

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13169
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035160228854 : ℝ) ≤ wn 13169 := by
  have hn : √(13169 : ℝ) ≤ 114.756263445618 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13169 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.756263445618 ≤ 2 / √(13169 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242758201 : ℝ) ≤ rhoBar 13169 BstLean.Part154.csC ∧
    rhoBar 13169 BstLean.Part154.csC ≤ 0.000242758577 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035160228854 : ℝ) / (1.295212 * 13169) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035160228855 : ℝ) / (1.29521 * 13169) := by gcongr
      _ ≤ (0.000242758577 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13169 BstLean.Part154.csC) ≤ 0.000971093240 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13169 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) ≤ 0.000185420326 ∧
    cc1 (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) ≤ 0.000117984249 ∧
    cc2 (rhoBar 13169 BstLean.Part154.csC) ≤ 0.000068490839 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13169 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13169 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13169 BstLean.Part154.csC * nuR (rhoBar 13169 BstLean.Part154.csC)) ≤ 0.000485531887 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242758577 : ℝ) * 0.000971093240 := by gcongr
      _ ≤ (0.000485531887 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13169 BstLean.Part154.csC) * nuR (rhoBar 13169 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971093240 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13169 BstLean.Part154.csC) * rhoBar 13169 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242758577 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242758577 / 2 + 0.399 * 0.000971093240 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185420326 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485531887 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117984249 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242758577 / 1.414213562 := by gcongr
      _ ≤ (0.000068490839 : ℝ) := by norm_num

end BstLean.Part269.N13169

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13169
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) ≤ 1.48474E-7 := by
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13169 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13169 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13169 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185420326 : ℝ) ^ 2 + 0.000117984249 ^ 2 + 3 * 0.000068490839 ^ 2 +
        2 * 0.797885 * 0.000185420326 * 0.000117984249 + 2 * 0.000185420326 * 0.000068490839 +
        4 * 0.797885 * 0.000117984249 * 0.000068490839 := by gcongr
    _ ≤ (1.48474E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13169 BstLean.Part154.csC Θ ≤ 0.002532468592 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13169 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13169 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13169 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035160228855 * 1.48474E-7 / (0.000242758201 : ℝ) := by gcongr
    _ ≤ 0.002532468592 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13169 BstLean.Part154.csC Θ ≤ 0.002808148676 + 0.000639915111 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13169 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13169 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035160228855 : ℝ) * ((2 * Θ * 0.000242758577 +
        (6863 / 10000) * 0.000242758577 * 13169 * 0.000971093240) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002808148676 + 0.000639915111 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13169 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13169 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13169 0.011 Θ ∧ gammaRatio 13169 0.011 Θ ≤ 0.000083454122 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13169 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035160228855 : ℝ) * 0.525 / ((1 - 0.011) * 13169) := by gcongr
      _ ≤ (0.000083454122 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13169 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13169 0.011 Θ) :=
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
    badAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13169 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13169 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13169 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13169 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13169 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13169 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13169 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13169 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13169 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13169 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035160228855 : ℝ) * 13169 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003125033834 + 0.003172383703 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13169

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13169
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13169 BstLean.Part154.csC) (piBar (rhoBar 13169 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13169 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13169 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13169 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13169 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13169 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13169 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13169 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13169 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13169 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13169 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051531211247 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13169) ≤ 0.010406731147 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13169 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035160228855)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010406731147 + 2 * 0.737676 / 13169) := by gcongr
    _ ≤ (0.051531211247 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13169 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13169

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13169
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524022507 : ℝ) ≤ plow 13169 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13169) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297135279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329546011) : eMP 13169 0.011 xi bn ≤ 0.001145229201 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13169 : ℝ) * (1 - 0.011))) ≤ 0.000566307224 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329546011 / (13169 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566307224 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566307224 : ℝ) + 3.141593 * 0.052297135279 / (13169 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145229201 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297135279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329546011) : PiBarMP 13169 12 0.011 xi bn ≤ 0.158325267476 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13169 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036462940241 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.123358695755 : ℝ) ≤ √((13169 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.756263445617 : ℝ) ≤ √(13169 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13169) ≤ 0.121408695652 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036462940241 + 0.052297135279 * 1.772454 / (2 * (114.123358695755 : ℝ))) * (1 + 0.001145229201) +
        8 / (13169 * 114.756263445617) + 0.121408695652 := by gcongr
    _ ≤ (0.158325267476 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297135279)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329546011) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280216880407) :
    parallelOracle 13169 0.011 xi bn cd ≤ 0.159280491000 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13169 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13169 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524022507 : ℝ) ≤ plow 13169 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.756263445617 : ℝ) ≤ √(13169 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280216880407 : ℝ) / (2 * 0.560524022507 * 114.756263445617)) * 0.158325267476 +
        0.280216880407 ^ 2 / (2 * 0.560524022507 * 114.756263445617) := by gcongr
    _ ≤ (0.159280491000 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052297135279) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329546011)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280216880407) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13169 13169 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524022507 : ℝ) ≤ plow 13169 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.756263445617 : ℝ) ≤ √(13169 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13169 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13169 Θ 1.22 ≤ 0.011555800618 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.756263445617 := by gcongr <;> linarith
      _ ≤ (0.011555800618 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13169 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13169 13169 0.011 ≤ 0.008329714384 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13169 13169 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13169 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13169 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13169 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13169 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159280491000 + 0.011555800618 + (0.008329714384 : ℝ) *
        (1 + 2 * (0.280216880407 + 0.011555800618) / (0.560524022507 * 114.756263445617))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13169]

end BstLean.Part269.N13169

/-! The original eight local profiles supply actual 13169 moment certificates. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13169 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052297135279 ∧
    0 ≤ bN 13169 BstLean.Part154.csC (groupTheta g) ∧ bN 13169 BstLean.Part154.csC (groupTheta g) ≤ 0.001329546011 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13169 13169 0.011
      (momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13169 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13169 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13169 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228685669160 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13169 0.011
      (momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13169 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13169
/-! The actual computed-centre upper energy formula at 13169. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13169

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13169)
open BstLean.Part268 (cell13169)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084228531835
  | 2 => 0.085151743666
  | 3 => 0.086070367178
  | 4 => 0.086985177761
  | 5 => 0.087897131336
  | 6 => 0.088807393352
  | 7 => 0.089717370933
  | 8 => 0.090628748290
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13169 13169 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13169 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13169

/-! Actual upper energy certificates on all 43 source endpoints at 13169. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13169)
open BstLean.Part268 (cell13169)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13169 (gMinus 13169) (1 - (cell13169 i).lower) ≤ 1 ∧
    energyUpper 13169 (gMinus 13169) (BstLean.Part211.gPlus 13169)
      (finiteEnergy 13169 13169 0.011) (1 - (cell13169 i).lower) ≤
      (cell13169 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨10,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨11,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨12,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨13,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨14,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨15,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨16,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨17,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨18,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨19,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨20,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨21,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨22,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨23,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨24,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨25,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨26,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨27,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨28,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨29,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨30,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨31,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨32,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨33,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨34,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨35,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨36,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨37,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨38,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨39,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨40,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨41,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨42,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨43,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨44,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨45,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨46,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨47,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨48,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨49,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨50,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨51,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13169) (by norm_num)
        (q := 1 - (cell13169 ⟨52,by decide⟩).lower)
        (by norm_num [cell13169]) (by norm_num [cell13169])
      exact ⟨E.1,E.2.trans (by norm_num [cell13169])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13169

/-! Source-cell containment and simple scalar guards at 13169. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13169)
open BstLean.Part268 (cell13169)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13169 ⟨10,by decide⟩).lower ∧ (cell13169 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13169 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13169 ⟨11,by decide⟩).lower ∧ (cell13169 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13169 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13169 ⟨12,by decide⟩).lower ∧ (cell13169 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13169 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13169 ⟨13,by decide⟩).lower ∧ (cell13169 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13169 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13169 ⟨14,by decide⟩).lower ∧ (cell13169 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13169 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13169 ⟨15,by decide⟩).lower ∧ (cell13169 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13169 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13169 ⟨16,by decide⟩).lower ∧ (cell13169 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13169 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13169 ⟨17,by decide⟩).lower ∧ (cell13169 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13169 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13169 ⟨18,by decide⟩).lower ∧ (cell13169 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13169 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13169 ⟨19,by decide⟩).lower ∧ (cell13169 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13169 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13169 ⟨20,by decide⟩).lower ∧ (cell13169 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13169 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13169 ⟨21,by decide⟩).lower ∧ (cell13169 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13169 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13169 ⟨22,by decide⟩).lower ∧ (cell13169 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13169 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13169 ⟨23,by decide⟩).lower ∧ (cell13169 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13169 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13169 ⟨24,by decide⟩).lower ∧ (cell13169 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13169 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13169 ⟨25,by decide⟩).lower ∧ (cell13169 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13169 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13169 ⟨26,by decide⟩).lower ∧ (cell13169 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13169 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13169 ⟨27,by decide⟩).lower ∧ (cell13169 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13169 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13169 ⟨28,by decide⟩).lower ∧ (cell13169 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13169 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13169 ⟨29,by decide⟩).lower ∧ (cell13169 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13169 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13169 ⟨30,by decide⟩).lower ∧ (cell13169 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13169 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13169 ⟨31,by decide⟩).lower ∧ (cell13169 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13169 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13169 ⟨32,by decide⟩).lower ∧ (cell13169 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13169 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13169 ⟨33,by decide⟩).lower ∧ (cell13169 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13169 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13169 ⟨34,by decide⟩).lower ∧ (cell13169 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13169 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13169 ⟨35,by decide⟩).lower ∧ (cell13169 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13169 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13169 ⟨36,by decide⟩).lower ∧ (cell13169 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13169 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13169 ⟨37,by decide⟩).lower ∧ (cell13169 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13169 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13169 ⟨38,by decide⟩).lower ∧ (cell13169 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13169 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13169 ⟨39,by decide⟩).lower ∧ (cell13169 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13169 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13169 ⟨40,by decide⟩).lower ∧ (cell13169 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13169 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13169 ⟨41,by decide⟩).lower ∧ (cell13169 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13169 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13169 ⟨42,by decide⟩).lower ∧ (cell13169 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13169 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13169 ⟨43,by decide⟩).lower ∧ (cell13169 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13169 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13169 ⟨44,by decide⟩).lower ∧ (cell13169 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13169 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13169 ⟨45,by decide⟩).lower ∧ (cell13169 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13169 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13169 ⟨46,by decide⟩).lower ∧ (cell13169 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13169 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13169 ⟨47,by decide⟩).lower ∧ (cell13169 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13169 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13169 ⟨48,by decide⟩).lower ∧ (cell13169 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13169 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13169 ⟨49,by decide⟩).lower ∧ (cell13169 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13169 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13169 ⟨50,by decide⟩).lower ∧ (cell13169 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13169 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13169 ⟨51,by decide⟩).lower ∧ (cell13169 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13169 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13169 ⟨52,by decide⟩).lower ∧ (cell13169 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13169 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13169 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13169 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13169,cell13169,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13169 i).lower ∧
    (cell13169 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13169 i).upper ≤ (0.532 : ℝ) ∧
    (cell13169 i).centre ≤ (0.1 : ℝ) ∧ (cell13169 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13169 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13169 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13169

/-! The local source numeric instances at 13169 have no network premises. -/
namespace BstLean.Part269.N13169
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13169)
open BstLean.Part268 (cell13169)

noncomputable def sourceNumerics13169 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13169 (cell13169 i)
      scalarRow13169.M scalarRow13169.H scalarRow13169.xi := by
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
    energy_allowance := scalarRow13169.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13169]
    centre_nonneg := (scalarRow13169.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13169])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13169
/-! Actual 13170 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13170 ≤ (1.035158882437 : ℝ) := by
  have hr : (114.760620423558 : ℝ) ≤ √(13170 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.760620423558 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13170 13170 (11 / 1000) ≤
    (0.008329398137 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13170) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.760620423558 : ℝ) ≤ √(13170 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13170)
  have hdiv : K / √(13170 : ℝ) ≤ K / 114.760620423558 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.760620423558 ≤ (0.008329398137 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13170.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13170 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13170 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13170 := gPlus_lower 13170
end BstLean.Part269.N13170

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13170
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035158882436 : ℝ) ≤ wn 13170 := by
  have hn : √(13170 : ℝ) ≤ 114.760620423559 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13170 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.760620423559 ≤ 2 / √(13170 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242739453 : ℝ) ≤ rhoBar 13170 BstLean.Part154.csC ∧
    rhoBar 13170 BstLean.Part154.csC ≤ 0.000242739829 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035158882436 : ℝ) / (1.295212 * 13170) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035158882437 : ℝ) / (1.29521 * 13170) := by gcongr
      _ ≤ (0.000242739829 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13170 BstLean.Part154.csC) ≤ 0.000971018239 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13170 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) ≤ 0.000185406006 ∧
    cc1 (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) ≤ 0.000117975137 ∧
    cc2 (rhoBar 13170 BstLean.Part154.csC) ≤ 0.000068485549 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13170 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13170 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13170 BstLean.Part154.csC * nuR (rhoBar 13170 BstLean.Part154.csC)) ≤ 0.000485494389 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242739829 : ℝ) * 0.000971018239 := by gcongr
      _ ≤ (0.000485494389 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13170 BstLean.Part154.csC) * nuR (rhoBar 13170 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971018239 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13170 BstLean.Part154.csC) * rhoBar 13170 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242739829 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242739829 / 2 + 0.399 * 0.000971018239 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185406006 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485494389 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117975137 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242739829 / 1.414213562 := by gcongr
      _ ≤ (0.000068485549 : ℝ) := by norm_num

end BstLean.Part269.N13170

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13170
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) ≤ 1.48451E-7 := by
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13170 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13170 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13170 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185406006 : ℝ) ^ 2 + 0.000117975137 ^ 2 + 3 * 0.000068485549 ^ 2 +
        2 * 0.797885 * 0.000185406006 * 0.000117975137 + 2 * 0.000185406006 * 0.000068485549 +
        4 * 0.797885 * 0.000117975137 * 0.000068485549 := by gcongr
    _ ≤ (1.48451E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13170 BstLean.Part154.csC Θ ≤ 0.002532268560 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13170 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13170 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13170 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035158882437 * 1.48451E-7 / (0.000242739453 : ℝ) := by gcongr
    _ ≤ 0.002532268560 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13170 BstLean.Part154.csC Θ ≤ 0.002807924493 + 0.000639864859 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13170 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13170 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035158882437 : ℝ) * ((2 * Θ * 0.000242739829 +
        (6863 / 10000) * 0.000242739829 * 13170 * 0.000971018239) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002807924493 + 0.000639864859 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13170 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13170 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13170 0.011 Θ ∧ gammaRatio 13170 0.011 Θ ≤ 0.000083447676 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13170 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035158882437 : ℝ) * 0.525 / ((1 - 0.011) * 13170) := by gcongr
      _ ≤ (0.000083447676 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13170 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13170 0.011 Θ) :=
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
    badAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13170 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13170 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13170 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13170 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13170 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13170 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13170 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13170 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13170 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13170 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035158882437 : ℝ) * 13170 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003124809651 + 0.003172133419 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13170

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13170
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13170 BstLean.Part154.csC) (piBar (rhoBar 13170 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13170 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13170 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13170 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13170 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13170 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13170 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13170 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13170 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13170 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13170 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051529233986 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13170) ≤ 0.010406336047 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13170 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035158882437)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010406336047 + 2 * 0.737676 / 13170) := by gcongr
    _ ≤ (0.051529233986 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13170 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13170

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13170
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524064563 : ℝ) ≤ plow 13170 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13170) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296779696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329440994) : eMP 13170 0.011 xi bn ≤ 0.001145140427 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13170 : ℝ) * (1 - 0.011))) ≤ 0.000566263359 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329440994 / (13170 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566263359 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566263359 : ℝ) + 3.141593 * 0.052296779696 / (13170 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145140427 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296779696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329440994) : PiBarMP 13170 12 0.011 xi bn ≤ 0.158319194294 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13170 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036461500162 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.127691644052 : ℝ) ≤ √((13170 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.760620423558 : ℝ) ≤ √(13170 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13170) ≤ 0.121404086274 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036461500162 + 0.052296779696 * 1.772454 / (2 * (114.127691644052 : ℝ))) * (1 + 0.001145140427) +
        8 / (13170 * 114.760620423558) + 0.121404086274 := by gcongr
    _ ≤ (0.158319194294 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296779696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329440994) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280214125696) :
    parallelOracle 13170 0.011 xi bn cd ≤ 0.159274352862 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13170 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13170 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524064563 : ℝ) ≤ plow 13170 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.760620423558 : ℝ) ≤ √(13170 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280214125696 : ℝ) / (2 * 0.560524064563 * 114.760620423558)) * 0.158319194294 +
        0.280214125696 ^ 2 / (2 * 0.560524064563 * 114.760620423558) := by gcongr
    _ ≤ (0.159274352862 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296779696) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329440994)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280214125696) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13170 13170 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524064563 : ℝ) ≤ plow 13170 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.760620423558 : ℝ) ≤ √(13170 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13170 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13170 Θ 1.22 ≤ 0.011555361893 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.760620423558 := by gcongr <;> linarith
      _ ≤ (0.011555361893 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13170 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13170 13170 0.011 ≤ 0.008329398137 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13170 13170 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13170 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13170 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13170 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13170 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159274352862 + 0.011555361893 + (0.008329398137 : ℝ) *
        (1 + 2 * (0.280214125696 + 0.011555361893) / (0.560524064563 * 114.760620423558))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13170]

end BstLean.Part269.N13170

/-! The original eight local profiles supply actual 13170 moment certificates. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13170 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052296779696 ∧
    0 ≤ bN 13170 BstLean.Part154.csC (groupTheta g) ∧ bN 13170 BstLean.Part154.csC (groupTheta g) ≤ 0.001329440994 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13170 13170 0.011
      (momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13170 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13170 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13170 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228684891710 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13170 0.011
      (momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13170 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13170
/-! The actual computed-centre upper energy formula at 13170. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13170

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13170)
open BstLean.Part268 (cell13170)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084226040110
  | 2 => 0.085149221724
  | 3 => 0.086067810808
  | 4 => 0.086982581741
  | 5 => 0.087894489243
  | 6 => 0.088804697348
  | 7 => 0.089714611520
  | 8 => 0.090625914041
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13170 13170 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13170 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13170

/-! Actual upper energy certificates on all 43 source endpoints at 13170. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13170)
open BstLean.Part268 (cell13170)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13170 (gMinus 13170) (1 - (cell13170 i).lower) ≤ 1 ∧
    energyUpper 13170 (gMinus 13170) (BstLean.Part211.gPlus 13170)
      (finiteEnergy 13170 13170 0.011) (1 - (cell13170 i).lower) ≤
      (cell13170 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨10,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨11,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨12,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨13,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨14,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨15,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨16,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨17,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨18,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨19,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨20,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨21,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨22,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨23,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨24,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨25,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨26,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨27,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨28,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨29,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨30,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨31,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨32,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨33,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨34,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨35,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨36,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨37,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨38,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨39,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨40,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨41,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨42,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨43,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨44,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨45,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨46,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨47,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨48,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨49,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨50,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨51,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13170) (by norm_num)
        (q := 1 - (cell13170 ⟨52,by decide⟩).lower)
        (by norm_num [cell13170]) (by norm_num [cell13170])
      exact ⟨E.1,E.2.trans (by norm_num [cell13170])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13170

/-! Source-cell containment and simple scalar guards at 13170. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13170)
open BstLean.Part268 (cell13170)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13170 ⟨10,by decide⟩).lower ∧ (cell13170 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13170 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13170 ⟨11,by decide⟩).lower ∧ (cell13170 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13170 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13170 ⟨12,by decide⟩).lower ∧ (cell13170 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13170 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13170 ⟨13,by decide⟩).lower ∧ (cell13170 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13170 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13170 ⟨14,by decide⟩).lower ∧ (cell13170 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13170 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13170 ⟨15,by decide⟩).lower ∧ (cell13170 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13170 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13170 ⟨16,by decide⟩).lower ∧ (cell13170 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13170 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13170 ⟨17,by decide⟩).lower ∧ (cell13170 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13170 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13170 ⟨18,by decide⟩).lower ∧ (cell13170 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13170 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13170 ⟨19,by decide⟩).lower ∧ (cell13170 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13170 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13170 ⟨20,by decide⟩).lower ∧ (cell13170 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13170 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13170 ⟨21,by decide⟩).lower ∧ (cell13170 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13170 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13170 ⟨22,by decide⟩).lower ∧ (cell13170 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13170 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13170 ⟨23,by decide⟩).lower ∧ (cell13170 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13170 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13170 ⟨24,by decide⟩).lower ∧ (cell13170 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13170 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13170 ⟨25,by decide⟩).lower ∧ (cell13170 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13170 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13170 ⟨26,by decide⟩).lower ∧ (cell13170 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13170 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13170 ⟨27,by decide⟩).lower ∧ (cell13170 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13170 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13170 ⟨28,by decide⟩).lower ∧ (cell13170 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13170 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13170 ⟨29,by decide⟩).lower ∧ (cell13170 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13170 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13170 ⟨30,by decide⟩).lower ∧ (cell13170 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13170 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13170 ⟨31,by decide⟩).lower ∧ (cell13170 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13170 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13170 ⟨32,by decide⟩).lower ∧ (cell13170 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13170 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13170 ⟨33,by decide⟩).lower ∧ (cell13170 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13170 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13170 ⟨34,by decide⟩).lower ∧ (cell13170 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13170 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13170 ⟨35,by decide⟩).lower ∧ (cell13170 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13170 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13170 ⟨36,by decide⟩).lower ∧ (cell13170 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13170 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13170 ⟨37,by decide⟩).lower ∧ (cell13170 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13170 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13170 ⟨38,by decide⟩).lower ∧ (cell13170 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13170 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13170 ⟨39,by decide⟩).lower ∧ (cell13170 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13170 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13170 ⟨40,by decide⟩).lower ∧ (cell13170 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13170 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13170 ⟨41,by decide⟩).lower ∧ (cell13170 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13170 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13170 ⟨42,by decide⟩).lower ∧ (cell13170 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13170 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13170 ⟨43,by decide⟩).lower ∧ (cell13170 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13170 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13170 ⟨44,by decide⟩).lower ∧ (cell13170 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13170 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13170 ⟨45,by decide⟩).lower ∧ (cell13170 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13170 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13170 ⟨46,by decide⟩).lower ∧ (cell13170 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13170 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13170 ⟨47,by decide⟩).lower ∧ (cell13170 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13170 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13170 ⟨48,by decide⟩).lower ∧ (cell13170 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13170 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13170 ⟨49,by decide⟩).lower ∧ (cell13170 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13170 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13170 ⟨50,by decide⟩).lower ∧ (cell13170 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13170 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13170 ⟨51,by decide⟩).lower ∧ (cell13170 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13170 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13170 ⟨52,by decide⟩).lower ∧ (cell13170 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13170 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13170 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13170 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13170,cell13170,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13170 i).lower ∧
    (cell13170 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13170 i).upper ≤ (0.532 : ℝ) ∧
    (cell13170 i).centre ≤ (0.1 : ℝ) ∧ (cell13170 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13170 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13170 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13170

/-! The local source numeric instances at 13170 have no network premises. -/
namespace BstLean.Part269.N13170
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13170)
open BstLean.Part268 (cell13170)

noncomputable def sourceNumerics13170 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13170 (cell13170 i)
      scalarRow13170.M scalarRow13170.H scalarRow13170.xi := by
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
    energy_allowance := scalarRow13170.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13170]
    centre_nonneg := (scalarRow13170.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13170])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13170
/-! Actual 13171 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13171 ≤ (1.035157536174 : ℝ) := by
  have hr : (114.764977236088 : ℝ) ≤ √(13171 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.764977236088 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13171 13171 (11 / 1000) ≤
    (0.008329081927 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13171) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.764977236088 : ℝ) ≤ √(13171 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13171)
  have hdiv : K / √(13171 : ℝ) ≤ K / 114.764977236088 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.764977236088 ≤ (0.008329081927 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13171.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13171 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13171 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13171 := gPlus_lower 13171
end BstLean.Part269.N13171

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13171
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035157536173 : ℝ) ≤ wn 13171 := by
  have hn : √(13171 : ℝ) ≤ 114.764977236089 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13171 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.764977236089 ≤ 2 / √(13171 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242720708 : ℝ) ≤ rhoBar 13171 BstLean.Part154.csC ∧
    rhoBar 13171 BstLean.Part154.csC ≤ 0.000242721083 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035157536173 : ℝ) / (1.295212 * 13171) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035157536174 : ℝ) / (1.29521 * 13171) := by gcongr
      _ ≤ (0.000242721083 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13171 BstLean.Part154.csC) ≤ 0.000970943246 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13171 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) ≤ 0.000185391687 ∧
    cc1 (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) ≤ 0.000117966026 ∧
    cc2 (rhoBar 13171 BstLean.Part154.csC) ≤ 0.000068480260 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13171 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13171 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13171 BstLean.Part154.csC * nuR (rhoBar 13171 BstLean.Part154.csC)) ≤ 0.000485456895 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242721083 : ℝ) * 0.000970943246 := by gcongr
      _ ≤ (0.000485456895 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13171 BstLean.Part154.csC) * nuR (rhoBar 13171 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970943246 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13171 BstLean.Part154.csC) * rhoBar 13171 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242721083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242721083 / 2 + 0.399 * 0.000970943246 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185391687 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485456895 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117966026 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242721083 / 1.414213562 := by gcongr
      _ ≤ (0.000068480260 : ℝ) := by norm_num

end BstLean.Part269.N13171

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13171
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) ≤ 1.48428E-7 := by
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13171 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13171 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13171 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185391687 : ℝ) ^ 2 + 0.000117966026 ^ 2 + 3 * 0.000068480260 ^ 2 +
        2 * 0.797885 * 0.000185391687 * 0.000117966026 + 2 * 0.000185391687 * 0.000068480260 +
        4 * 0.797885 * 0.000117966026 * 0.000068480260 := by gcongr
    _ ≤ (1.48428E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13171 BstLean.Part154.csC Θ ≤ 0.002532068468 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13171 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13171 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13171 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035157536174 * 1.48428E-7 / (0.000242720708 : ℝ) := by gcongr
    _ ≤ 0.002532068468 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13171 BstLean.Part154.csC Θ ≤ 0.002807700325 + 0.000639814612 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13171 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13171 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035157536174 : ℝ) * ((2 * Θ * 0.000242721083 +
        (6863 / 10000) * 0.000242721083 * 13171 * 0.000970943246) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002807700325 + 0.000639814612 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13171 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13171 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13171 0.011 Θ ∧ gammaRatio 13171 0.011 Θ ≤ 0.000083441232 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13171 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035157536174 : ℝ) * 0.525 / ((1 - 0.011) * 13171) := by gcongr
      _ ≤ (0.000083441232 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13171 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13171 0.011 Θ) :=
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
    badAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13171 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13171 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13171 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13171 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13171 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13171 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13171 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13171 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13171 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13171 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035157536174 : ℝ) * 13171 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003124585483 + 0.003171883080 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13171

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13171
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13171 BstLean.Part154.csC) (piBar (rhoBar 13171 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13171 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13171 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13171 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13171 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13171 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13171 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13171 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13171 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13171 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13171 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051527256952 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13171) ≤ 0.010405940992 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13171 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035157536174)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010405940992 + 2 * 0.737676 / 13171) := by gcongr
    _ ≤ (0.051527256952 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13171 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13171

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13171
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524106613 : ℝ) ≤ plow 13171 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13171) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296424100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329335946) : eMP 13171 0.011 xi bn ≤ 0.001145051646 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13171 : ℝ) * (1 - 0.011))) ≤ 0.000566219490 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329335946 / (13171 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566219490 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566219490 : ℝ) + 3.141593 * 0.052296424100 / (13171 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145051646 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296424100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329335946) : PiBarMP 13171 12 0.011 xi bn ≤ 0.158313121156 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13171 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036460059600 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.132024427852 : ℝ) ≤ √((13171 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.764977236088 : ℝ) ≤ √(13171 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13171) ≤ 0.121399477422 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036460059600 + 0.052296424100 * 1.772454 / (2 * (114.132024427852 : ℝ))) * (1 + 0.001145051646) +
        8 / (13171 * 114.764977236088) + 0.121399477422 := by gcongr
    _ ≤ (0.158313121156 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296424100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329335946) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280211371180) :
    parallelOracle 13171 0.011 xi bn cd ≤ 0.159268214777 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13171 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13171 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524106613 : ℝ) ≤ plow 13171 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.764977236088 : ℝ) ≤ √(13171 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280211371180 : ℝ) / (2 * 0.560524106613 * 114.764977236088)) * 0.158313121156 +
        0.280211371180 ^ 2 / (2 * 0.560524106613 * 114.764977236088) := by gcongr
    _ ≤ (0.159268214777 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296424100) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329335946)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280211371180) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13171 13171 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524106613 : ℝ) ≤ plow 13171 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.764977236088 : ℝ) ≤ √(13171 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13171 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13171 Θ 1.22 ≤ 0.011554923218 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.764977236088 := by gcongr <;> linarith
      _ ≤ (0.011554923218 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13171 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13171 13171 0.011 ≤ 0.008329081927 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13171 13171 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13171 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13171 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13171 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13171 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159268214777 + 0.011554923218 + (0.008329081927 : ℝ) *
        (1 + 2 * (0.280211371180 + 0.011554923218) / (0.560524106613 * 114.764977236088))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13171]

end BstLean.Part269.N13171

/-! The original eight local profiles supply actual 13171 moment certificates. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13171 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052296424100 ∧
    0 ≤ bN 13171 BstLean.Part154.csC (groupTheta g) ∧ bN 13171 BstLean.Part154.csC (groupTheta g) ≤ 0.001329335946 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13171 13171 0.011
      (momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13171 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13171 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13171 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228684114228 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13171 0.011
      (momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13171 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13171
/-! The actual computed-centre upper energy formula at 13171. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13171

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13171)
open BstLean.Part268 (cell13171)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084223549078
  | 2 => 0.085146700498
  | 3 => 0.086065255183
  | 4 => 0.086979986501
  | 5 => 0.087891847973
  | 6 => 0.088802002219
  | 7 => 0.089711853048
  | 8 => 0.090623080812
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13171 13171 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13171 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13171

/-! Actual upper energy certificates on all 43 source endpoints at 13171. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13171)
open BstLean.Part268 (cell13171)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13171 (gMinus 13171) (1 - (cell13171 i).lower) ≤ 1 ∧
    energyUpper 13171 (gMinus 13171) (BstLean.Part211.gPlus 13171)
      (finiteEnergy 13171 13171 0.011) (1 - (cell13171 i).lower) ≤
      (cell13171 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨10,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨11,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨12,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨13,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨14,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨15,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨16,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨17,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨18,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨19,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨20,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨21,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨22,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨23,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨24,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨25,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨26,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨27,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨28,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨29,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨30,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨31,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨32,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨33,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨34,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨35,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨36,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨37,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨38,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨39,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨40,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨41,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨42,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨43,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨44,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨45,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨46,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨47,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨48,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨49,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨50,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨51,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13171) (by norm_num)
        (q := 1 - (cell13171 ⟨52,by decide⟩).lower)
        (by norm_num [cell13171]) (by norm_num [cell13171])
      exact ⟨E.1,E.2.trans (by norm_num [cell13171])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13171

/-! Source-cell containment and simple scalar guards at 13171. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13171)
open BstLean.Part268 (cell13171)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13171 ⟨10,by decide⟩).lower ∧ (cell13171 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13171 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13171 ⟨11,by decide⟩).lower ∧ (cell13171 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13171 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13171 ⟨12,by decide⟩).lower ∧ (cell13171 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13171 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13171 ⟨13,by decide⟩).lower ∧ (cell13171 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13171 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13171 ⟨14,by decide⟩).lower ∧ (cell13171 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13171 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13171 ⟨15,by decide⟩).lower ∧ (cell13171 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13171 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13171 ⟨16,by decide⟩).lower ∧ (cell13171 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13171 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13171 ⟨17,by decide⟩).lower ∧ (cell13171 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13171 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13171 ⟨18,by decide⟩).lower ∧ (cell13171 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13171 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13171 ⟨19,by decide⟩).lower ∧ (cell13171 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13171 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13171 ⟨20,by decide⟩).lower ∧ (cell13171 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13171 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13171 ⟨21,by decide⟩).lower ∧ (cell13171 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13171 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13171 ⟨22,by decide⟩).lower ∧ (cell13171 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13171 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13171 ⟨23,by decide⟩).lower ∧ (cell13171 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13171 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13171 ⟨24,by decide⟩).lower ∧ (cell13171 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13171 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13171 ⟨25,by decide⟩).lower ∧ (cell13171 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13171 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13171 ⟨26,by decide⟩).lower ∧ (cell13171 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13171 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13171 ⟨27,by decide⟩).lower ∧ (cell13171 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13171 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13171 ⟨28,by decide⟩).lower ∧ (cell13171 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13171 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13171 ⟨29,by decide⟩).lower ∧ (cell13171 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13171 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13171 ⟨30,by decide⟩).lower ∧ (cell13171 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13171 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13171 ⟨31,by decide⟩).lower ∧ (cell13171 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13171 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13171 ⟨32,by decide⟩).lower ∧ (cell13171 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13171 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13171 ⟨33,by decide⟩).lower ∧ (cell13171 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13171 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13171 ⟨34,by decide⟩).lower ∧ (cell13171 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13171 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13171 ⟨35,by decide⟩).lower ∧ (cell13171 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13171 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13171 ⟨36,by decide⟩).lower ∧ (cell13171 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13171 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13171 ⟨37,by decide⟩).lower ∧ (cell13171 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13171 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13171 ⟨38,by decide⟩).lower ∧ (cell13171 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13171 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13171 ⟨39,by decide⟩).lower ∧ (cell13171 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13171 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13171 ⟨40,by decide⟩).lower ∧ (cell13171 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13171 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13171 ⟨41,by decide⟩).lower ∧ (cell13171 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13171 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13171 ⟨42,by decide⟩).lower ∧ (cell13171 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13171 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13171 ⟨43,by decide⟩).lower ∧ (cell13171 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13171 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13171 ⟨44,by decide⟩).lower ∧ (cell13171 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13171 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13171 ⟨45,by decide⟩).lower ∧ (cell13171 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13171 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13171 ⟨46,by decide⟩).lower ∧ (cell13171 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13171 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13171 ⟨47,by decide⟩).lower ∧ (cell13171 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13171 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13171 ⟨48,by decide⟩).lower ∧ (cell13171 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13171 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13171 ⟨49,by decide⟩).lower ∧ (cell13171 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13171 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13171 ⟨50,by decide⟩).lower ∧ (cell13171 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13171 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13171 ⟨51,by decide⟩).lower ∧ (cell13171 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13171 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13171 ⟨52,by decide⟩).lower ∧ (cell13171 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13171 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13171 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13171 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13171,cell13171,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13171 i).lower ∧
    (cell13171 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13171 i).upper ≤ (0.532 : ℝ) ∧
    (cell13171 i).centre ≤ (0.1 : ℝ) ∧ (cell13171 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13171 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13171 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13171

/-! The local source numeric instances at 13171 have no network premises. -/
namespace BstLean.Part269.N13171
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13171)
open BstLean.Part268 (cell13171)

noncomputable def sourceNumerics13171 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13171 (cell13171 i)
      scalarRow13171.M scalarRow13171.H scalarRow13171.xi := by
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
    energy_allowance := scalarRow13171.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13171]
    centre_nonneg := (scalarRow13171.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13171])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13171
/-! Actual 13172 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13172 ≤ (1.035156190065 : ℝ) := by
  have hr : (114.769333883228 : ℝ) ≤ √(13172 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.769333883228 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13172 13172 (11 / 1000) ≤
    (0.008328765752 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13172) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.769333883228 : ℝ) ≤ √(13172 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13172)
  have hdiv : K / √(13172 : ℝ) ≤ K / 114.769333883228 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.769333883228 ≤ (0.008328765752 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13172.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13172 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13172 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13172 := gPlus_lower 13172
end BstLean.Part269.N13172

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13172
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035156190064 : ℝ) ≤ wn 13172 := by
  have hn : √(13172 : ℝ) ≤ 114.769333883229 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13172 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.769333883229 ≤ 2 / √(13172 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242701965 : ℝ) ≤ rhoBar 13172 BstLean.Part154.csC ∧
    rhoBar 13172 BstLean.Part154.csC ≤ 0.000242702341 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035156190064 : ℝ) / (1.295212 * 13172) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035156190065 : ℝ) / (1.29521 * 13172) := by gcongr
      _ ≤ (0.000242702341 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13172 BstLean.Part154.csC) ≤ 0.000970868269 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13172 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) ≤ 0.000185377371 ∧
    cc1 (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) ≤ 0.000117956917 ∧
    cc2 (rhoBar 13172 BstLean.Part154.csC) ≤ 0.000068474972 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13172 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13172 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13172 BstLean.Part154.csC * nuR (rhoBar 13172 BstLean.Part154.csC)) ≤ 0.000485419409 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242702341 : ℝ) * 0.000970868269 := by gcongr
      _ ≤ (0.000485419409 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13172 BstLean.Part154.csC) * nuR (rhoBar 13172 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970868269 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13172 BstLean.Part154.csC) * rhoBar 13172 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242702341 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242702341 / 2 + 0.399 * 0.000970868269 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185377371 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485419409 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117956917 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242702341 / 1.414213562 := by gcongr
      _ ≤ (0.000068474972 : ℝ) := by norm_num

end BstLean.Part269.N13172

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13172
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) ≤ 1.48405E-7 := by
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13172 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13172 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13172 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185377371 : ℝ) ^ 2 + 0.000117956917 ^ 2 + 3 * 0.000068474972 ^ 2 +
        2 * 0.797885 * 0.000185377371 * 0.000117956917 + 2 * 0.000185377371 * 0.000068474972 +
        4 * 0.797885 * 0.000117956917 * 0.000068474972 := by gcongr
    _ ≤ (1.48405E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13172 BstLean.Part154.csC Θ ≤ 0.002531868325 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13172 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13172 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13172 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035156190065 * 1.48405E-7 / (0.000242701965 : ℝ) := by gcongr
    _ ≤ 0.002531868325 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13172 BstLean.Part154.csC Θ ≤ 0.002807476218 + 0.000639764376 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13172 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13172 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035156190065 : ℝ) * ((2 * Θ * 0.000242702341 +
        (6863 / 10000) * 0.000242702341 * 13172 * 0.000970868269) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002807476218 + 0.000639764376 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13172 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13172 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13172 0.011 Θ ∧ gammaRatio 13172 0.011 Θ ≤ 0.000083434789 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13172 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035156190065 : ℝ) * 0.525 / ((1 - 0.011) * 13172) := by gcongr
      _ ≤ (0.000083434789 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13172 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13172 0.011 Θ) :=
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
    badAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13172 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13172 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13172 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13172 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13172 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13172 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13172 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13172 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13172 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13172 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035156190065 : ℝ) * 13172 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003124361376 + 0.003171632701 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13172

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13172
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13172 BstLean.Part154.csC) (piBar (rhoBar 13172 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13172 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13172 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13172 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13172 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13172 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13172 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13172 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13172 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13172 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13172 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051525280150 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13172) ≤ 0.010405545983 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13172 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035156190065)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010405545983 + 2 * 0.737676 / 13172) := by gcongr
    _ ≤ (0.051525280150 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13172 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13172

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13172
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524148656 : ℝ) ≤ plow 13172 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13172) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296068545)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329230871) : eMP 13172 0.011 xi bn ≤ 0.001144962861 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13172 : ℝ) * (1 - 0.011))) ≤ 0.000566175619 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329230871 / (13172 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566175619 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566175619 : ℝ) + 3.141593 * 0.052296068545 / (13172 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144962861 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296068545)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329230871) : PiBarMP 13172 12 0.011 xi bn ≤ 0.158307048117 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13172 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036458618611 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.136357047174 : ℝ) ≤ √((13172 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.769333883228 : ℝ) ≤ √(13172 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13172) ≤ 0.121394869094 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036458618611 + 0.052296068545 * 1.772454 / (2 * (114.136357047174 : ℝ))) * (1 + 0.001144962861) +
        8 / (13172 * 114.769333883228) + 0.121394869094 := by gcongr
    _ ≤ (0.158307048117 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296068545)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329230871) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280208616983) :
    parallelOracle 13172 0.011 xi bn cd ≤ 0.159262076799 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13172 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13172 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524148656 : ℝ) ≤ plow 13172 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.769333883228 : ℝ) ≤ √(13172 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280208616983 : ℝ) / (2 * 0.560524148656 * 114.769333883228)) * 0.158307048117 +
        0.280208616983 ^ 2 / (2 * 0.560524148656 * 114.769333883228) := by gcongr
    _ ≤ (0.159262076799 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052296068545) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329230871)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280208616983) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13172 13172 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524148656 : ℝ) ≤ plow 13172 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.769333883228 : ℝ) ≤ √(13172 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13172 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13172 Θ 1.22 ≤ 0.011554484593 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.769333883228 := by gcongr <;> linarith
      _ ≤ (0.011554484593 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13172 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13172 13172 0.011 ≤ 0.008328765752 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13172 13172 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13172 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13172 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13172 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13172 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159262076799 + 0.011554484593 + (0.008328765752 : ℝ) *
        (1 + 2 * (0.280208616983 + 0.011554484593) / (0.560524148656 * 114.769333883228))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13172]

end BstLean.Part269.N13172

/-! The original eight local profiles supply actual 13172 moment certificates. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13172 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052296068545 ∧
    0 ≤ bN 13172 BstLean.Part154.csC (groupTheta g) ∧ bN 13172 BstLean.Part154.csC (groupTheta g) ≤ 0.001329230871 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13172 13172 0.011
      (momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13172 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13172 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13172 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228683336833 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13172 0.011
      (momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13172 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13172
/-! The actual computed-centre upper energy formula at 13172. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13172

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13172)
open BstLean.Part268 (cell13172)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084221058738
  | 2 => 0.085144179987
  | 3 => 0.086062700302
  | 4 => 0.086977392040
  | 5 => 0.087889207526
  | 6 => 0.088799307967
  | 7 => 0.089709095515
  | 8 => 0.090620248599
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13172 13172 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13172 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13172

/-! Actual upper energy certificates on all 43 source endpoints at 13172. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13172)
open BstLean.Part268 (cell13172)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13172 (gMinus 13172) (1 - (cell13172 i).lower) ≤ 1 ∧
    energyUpper 13172 (gMinus 13172) (BstLean.Part211.gPlus 13172)
      (finiteEnergy 13172 13172 0.011) (1 - (cell13172 i).lower) ≤
      (cell13172 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨10,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨11,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨12,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨13,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨14,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨15,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨16,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨17,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨18,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨19,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨20,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨21,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨22,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨23,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨24,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨25,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨26,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨27,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨28,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨29,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨30,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨31,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨32,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨33,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨34,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨35,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨36,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨37,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨38,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨39,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨40,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨41,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨42,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨43,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨44,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨45,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨46,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨47,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨48,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨49,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨50,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨51,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13172) (by norm_num)
        (q := 1 - (cell13172 ⟨52,by decide⟩).lower)
        (by norm_num [cell13172]) (by norm_num [cell13172])
      exact ⟨E.1,E.2.trans (by norm_num [cell13172])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13172

/-! Source-cell containment and simple scalar guards at 13172. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13172)
open BstLean.Part268 (cell13172)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13172 ⟨10,by decide⟩).lower ∧ (cell13172 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13172 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13172 ⟨11,by decide⟩).lower ∧ (cell13172 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13172 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13172 ⟨12,by decide⟩).lower ∧ (cell13172 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13172 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13172 ⟨13,by decide⟩).lower ∧ (cell13172 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13172 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13172 ⟨14,by decide⟩).lower ∧ (cell13172 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13172 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13172 ⟨15,by decide⟩).lower ∧ (cell13172 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13172 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13172 ⟨16,by decide⟩).lower ∧ (cell13172 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13172 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13172 ⟨17,by decide⟩).lower ∧ (cell13172 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13172 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13172 ⟨18,by decide⟩).lower ∧ (cell13172 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13172 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13172 ⟨19,by decide⟩).lower ∧ (cell13172 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13172 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13172 ⟨20,by decide⟩).lower ∧ (cell13172 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13172 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13172 ⟨21,by decide⟩).lower ∧ (cell13172 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13172 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13172 ⟨22,by decide⟩).lower ∧ (cell13172 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13172 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13172 ⟨23,by decide⟩).lower ∧ (cell13172 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13172 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13172 ⟨24,by decide⟩).lower ∧ (cell13172 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13172 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13172 ⟨25,by decide⟩).lower ∧ (cell13172 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13172 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13172 ⟨26,by decide⟩).lower ∧ (cell13172 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13172 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13172 ⟨27,by decide⟩).lower ∧ (cell13172 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13172 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13172 ⟨28,by decide⟩).lower ∧ (cell13172 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13172 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13172 ⟨29,by decide⟩).lower ∧ (cell13172 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13172 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13172 ⟨30,by decide⟩).lower ∧ (cell13172 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13172 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13172 ⟨31,by decide⟩).lower ∧ (cell13172 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13172 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13172 ⟨32,by decide⟩).lower ∧ (cell13172 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13172 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13172 ⟨33,by decide⟩).lower ∧ (cell13172 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13172 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13172 ⟨34,by decide⟩).lower ∧ (cell13172 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13172 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13172 ⟨35,by decide⟩).lower ∧ (cell13172 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13172 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13172 ⟨36,by decide⟩).lower ∧ (cell13172 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13172 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13172 ⟨37,by decide⟩).lower ∧ (cell13172 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13172 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13172 ⟨38,by decide⟩).lower ∧ (cell13172 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13172 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13172 ⟨39,by decide⟩).lower ∧ (cell13172 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13172 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13172 ⟨40,by decide⟩).lower ∧ (cell13172 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13172 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13172 ⟨41,by decide⟩).lower ∧ (cell13172 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13172 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13172 ⟨42,by decide⟩).lower ∧ (cell13172 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13172 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13172 ⟨43,by decide⟩).lower ∧ (cell13172 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13172 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13172 ⟨44,by decide⟩).lower ∧ (cell13172 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13172 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13172 ⟨45,by decide⟩).lower ∧ (cell13172 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13172 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13172 ⟨46,by decide⟩).lower ∧ (cell13172 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13172 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13172 ⟨47,by decide⟩).lower ∧ (cell13172 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13172 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13172 ⟨48,by decide⟩).lower ∧ (cell13172 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13172 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13172 ⟨49,by decide⟩).lower ∧ (cell13172 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13172 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13172 ⟨50,by decide⟩).lower ∧ (cell13172 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13172 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13172 ⟨51,by decide⟩).lower ∧ (cell13172 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13172 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13172 ⟨52,by decide⟩).lower ∧ (cell13172 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13172 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13172 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13172 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13172,cell13172,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13172 i).lower ∧
    (cell13172 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13172 i).upper ≤ (0.532 : ℝ) ∧
    (cell13172 i).centre ≤ (0.1 : ℝ) ∧ (cell13172 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13172 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13172 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13172

/-! The local source numeric instances at 13172 have no network premises. -/
namespace BstLean.Part269.N13172
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13172)
open BstLean.Part268 (cell13172)

noncomputable def sourceNumerics13172 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13172 (cell13172 i)
      scalarRow13172.M scalarRow13172.H scalarRow13172.xi := by
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
    energy_allowance := scalarRow13172.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13172]
    centre_nonneg := (scalarRow13172.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13172])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13172
/-! Actual 13173 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13173 ≤ (1.035154844110 : ℝ) := by
  have hr : (114.773690364996 : ℝ) ≤ √(13173 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.773690364996 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13173 13173 (11 / 1000) ≤
    (0.008328449614 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13173) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.773690364996 : ℝ) ≤ √(13173 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13173)
  have hdiv : K / √(13173 : ℝ) ≤ K / 114.773690364996 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.773690364996 ≤ (0.008328449614 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13173.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13173 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13173 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13173 := gPlus_lower 13173
end BstLean.Part269.N13173

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13173
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035154844109 : ℝ) ≤ wn 13173 := by
  have hn : √(13173 : ℝ) ≤ 114.773690364997 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13173 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.773690364997 ≤ 2 / √(13173 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242683225 : ℝ) ≤ rhoBar 13173 BstLean.Part154.csC ∧
    rhoBar 13173 BstLean.Part154.csC ≤ 0.000242683601 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035154844109 : ℝ) / (1.295212 * 13173) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035154844110 : ℝ) / (1.29521 * 13173) := by gcongr
      _ ≤ (0.000242683601 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13173 BstLean.Part154.csC) ≤ 0.000970793300 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13173 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) ≤ 0.000185363057 ∧
    cc1 (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) ≤ 0.000117947809 ∧
    cc2 (rhoBar 13173 BstLean.Part154.csC) ≤ 0.000068469685 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13173 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13173 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13173 BstLean.Part154.csC * nuR (rhoBar 13173 BstLean.Part154.csC)) ≤ 0.000485381926 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242683601 : ℝ) * 0.000970793300 := by gcongr
      _ ≤ (0.000485381926 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13173 BstLean.Part154.csC) * nuR (rhoBar 13173 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970793300 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13173 BstLean.Part154.csC) * rhoBar 13173 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242683601 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242683601 / 2 + 0.399 * 0.000970793300 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185363057 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485381926 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117947809 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242683601 / 1.414213562 := by gcongr
      _ ≤ (0.000068469685 : ℝ) := by norm_num

end BstLean.Part269.N13173

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13173
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) ≤ 1.48382E-7 := by
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13173 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13173 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13173 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185363057 : ℝ) ^ 2 + 0.000117947809 ^ 2 + 3 * 0.000068469685 ^ 2 +
        2 * 0.797885 * 0.000185363057 * 0.000117947809 + 2 * 0.000185363057 * 0.000068469685 +
        4 * 0.797885 * 0.000117947809 * 0.000068469685 := by gcongr
    _ ≤ (1.48382E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13173 BstLean.Part154.csC Θ ≤ 0.002531668122 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13173 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13173 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13173 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035154844110 * 1.48382E-7 / (0.000242683225 : ℝ) := by gcongr
    _ ≤ 0.002531668122 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13173 BstLean.Part154.csC Θ ≤ 0.002807252126 + 0.000639714146 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13173 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13173 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035154844110 : ℝ) * ((2 * Θ * 0.000242683601 +
        (6863 / 10000) * 0.000242683601 * 13173 * 0.000970793300) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002807252126 + 0.000639714146 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13173 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13173 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13173 0.011 Θ ∧ gammaRatio 13173 0.011 Θ ≤ 0.000083428347 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13173 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035154844110 : ℝ) * 0.525 / ((1 - 0.011) * 13173) := by gcongr
      _ ≤ (0.000083428347 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13173 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13173 0.011 Θ) :=
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
    badAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13173 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13173 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13173 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13173 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13173 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13173 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13173 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13173 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13173 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13173 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035154844110 : ℝ) * 13173 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003124137284 + 0.003171382268 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13173

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13173
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13173 BstLean.Part154.csC) (piBar (rhoBar 13173 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13173 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13173 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13173 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13173 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13173 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13173 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13173 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13173 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13173 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13173 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051523303569 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13173) ≤ 0.010405151018 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13173 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035154844110)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010405151018 + 2 * 0.737676 / 13173) := by gcongr
    _ ≤ (0.051523303569 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13173 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13173

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13173
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524190693 : ℝ) ≤ plow 13173 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13173) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295712975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329125765) : eMP 13173 0.011 xi bn ≤ 0.001144874067 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13173 : ℝ) * (1 - 0.011))) ≤ 0.000566131744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329125765 / (13173 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566131744 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566131744 : ℝ) + 3.141593 * 0.052295712975 / (13173 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144874067 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295712975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329125765) : PiBarMP 13173 12 0.011 xi bn ≤ 0.158300975123 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13173 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036457177140 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.140689502035 : ℝ) ≤ √((13173 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.773690364996 : ℝ) ≤ √(13173 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13173) ≤ 0.121390261292 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036457177140 + 0.052295712975 * 1.772454 / (2 * (114.140689502035 : ℝ))) * (1 + 0.001144874067) +
        8 / (13173 * 114.773690364996) + 0.121390261292 := by gcongr
    _ ≤ (0.158300975123 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295712975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329125765) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280205862972) :
    parallelOracle 13173 0.011 xi bn cd ≤ 0.159255938874 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13173 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13173 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524190693 : ℝ) ≤ plow 13173 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.773690364996 : ℝ) ≤ √(13173 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280205862972 : ℝ) / (2 * 0.560524190693 * 114.773690364996)) * 0.158300975123 +
        0.280205862972 ^ 2 / (2 * 0.560524190693 * 114.773690364996) := by gcongr
    _ ≤ (0.159255938874 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295712975) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329125765)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280205862972) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13173 13173 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524190693 : ℝ) ≤ plow 13173 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.773690364996 : ℝ) ≤ √(13173 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13173 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13173 Θ 1.22 ≤ 0.011554046017 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.773690364996 := by gcongr <;> linarith
      _ ≤ (0.011554046017 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13173 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13173 13173 0.011 ≤ 0.008328449614 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13173 13173 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13173 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13173 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13173 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13173 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159255938874 + 0.011554046017 + (0.008328449614 : ℝ) *
        (1 + 2 * (0.280205862972 + 0.011554046017) / (0.560524190693 * 114.773690364996))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13173]

end BstLean.Part269.N13173

/-! The original eight local profiles supply actual 13173 moment certificates. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13173 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052295712975 ∧
    0 ≤ bN 13173 BstLean.Part154.csC (groupTheta g) ∧ bN 13173 BstLean.Part154.csC (groupTheta g) ≤ 0.001329125765 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13173 13173 0.011
      (momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13173 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13173 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13173 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228682559403 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13173 0.011
      (momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13173 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13173
/-! The actual computed-centre upper energy formula at 13173. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13173

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13173)
open BstLean.Part268 (cell13173)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084218569091
  | 2 => 0.085141660192
  | 3 => 0.086060146164
  | 4 => 0.086974798358
  | 5 => 0.087886567901
  | 6 => 0.088796614588
  | 7 => 0.089706338922
  | 8 => 0.090617417404
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13173 13173 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13173 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13173

/-! Actual upper energy certificates on all 43 source endpoints at 13173. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13173)
open BstLean.Part268 (cell13173)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13173 (gMinus 13173) (1 - (cell13173 i).lower) ≤ 1 ∧
    energyUpper 13173 (gMinus 13173) (BstLean.Part211.gPlus 13173)
      (finiteEnergy 13173 13173 0.011) (1 - (cell13173 i).lower) ≤
      (cell13173 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨10,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨11,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨12,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨13,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨14,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨15,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨16,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨17,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨18,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨19,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨20,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨21,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨22,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨23,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨24,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨25,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨26,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨27,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨28,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨29,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨30,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨31,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨32,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨33,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨34,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨35,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨36,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨37,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨38,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨39,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨40,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨41,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨42,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨43,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨44,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨45,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨46,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨47,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨48,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨49,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨50,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨51,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13173) (by norm_num)
        (q := 1 - (cell13173 ⟨52,by decide⟩).lower)
        (by norm_num [cell13173]) (by norm_num [cell13173])
      exact ⟨E.1,E.2.trans (by norm_num [cell13173])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13173

/-! Source-cell containment and simple scalar guards at 13173. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13173)
open BstLean.Part268 (cell13173)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13173 ⟨10,by decide⟩).lower ∧ (cell13173 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13173 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13173 ⟨11,by decide⟩).lower ∧ (cell13173 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13173 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13173 ⟨12,by decide⟩).lower ∧ (cell13173 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13173 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13173 ⟨13,by decide⟩).lower ∧ (cell13173 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13173 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13173 ⟨14,by decide⟩).lower ∧ (cell13173 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13173 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13173 ⟨15,by decide⟩).lower ∧ (cell13173 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13173 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13173 ⟨16,by decide⟩).lower ∧ (cell13173 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13173 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13173 ⟨17,by decide⟩).lower ∧ (cell13173 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13173 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13173 ⟨18,by decide⟩).lower ∧ (cell13173 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13173 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13173 ⟨19,by decide⟩).lower ∧ (cell13173 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13173 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13173 ⟨20,by decide⟩).lower ∧ (cell13173 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13173 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13173 ⟨21,by decide⟩).lower ∧ (cell13173 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13173 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13173 ⟨22,by decide⟩).lower ∧ (cell13173 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13173 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13173 ⟨23,by decide⟩).lower ∧ (cell13173 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13173 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13173 ⟨24,by decide⟩).lower ∧ (cell13173 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13173 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13173 ⟨25,by decide⟩).lower ∧ (cell13173 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13173 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13173 ⟨26,by decide⟩).lower ∧ (cell13173 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13173 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13173 ⟨27,by decide⟩).lower ∧ (cell13173 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13173 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13173 ⟨28,by decide⟩).lower ∧ (cell13173 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13173 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13173 ⟨29,by decide⟩).lower ∧ (cell13173 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13173 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13173 ⟨30,by decide⟩).lower ∧ (cell13173 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13173 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13173 ⟨31,by decide⟩).lower ∧ (cell13173 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13173 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13173 ⟨32,by decide⟩).lower ∧ (cell13173 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13173 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13173 ⟨33,by decide⟩).lower ∧ (cell13173 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13173 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13173 ⟨34,by decide⟩).lower ∧ (cell13173 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13173 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13173 ⟨35,by decide⟩).lower ∧ (cell13173 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13173 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13173 ⟨36,by decide⟩).lower ∧ (cell13173 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13173 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13173 ⟨37,by decide⟩).lower ∧ (cell13173 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13173 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13173 ⟨38,by decide⟩).lower ∧ (cell13173 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13173 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13173 ⟨39,by decide⟩).lower ∧ (cell13173 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13173 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13173 ⟨40,by decide⟩).lower ∧ (cell13173 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13173 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13173 ⟨41,by decide⟩).lower ∧ (cell13173 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13173 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13173 ⟨42,by decide⟩).lower ∧ (cell13173 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13173 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13173 ⟨43,by decide⟩).lower ∧ (cell13173 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13173 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13173 ⟨44,by decide⟩).lower ∧ (cell13173 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13173 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13173 ⟨45,by decide⟩).lower ∧ (cell13173 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13173 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13173 ⟨46,by decide⟩).lower ∧ (cell13173 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13173 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13173 ⟨47,by decide⟩).lower ∧ (cell13173 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13173 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13173 ⟨48,by decide⟩).lower ∧ (cell13173 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13173 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13173 ⟨49,by decide⟩).lower ∧ (cell13173 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13173 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13173 ⟨50,by decide⟩).lower ∧ (cell13173 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13173 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13173 ⟨51,by decide⟩).lower ∧ (cell13173 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13173 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13173 ⟨52,by decide⟩).lower ∧ (cell13173 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13173 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13173 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13173 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13173,cell13173,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13173 i).lower ∧
    (cell13173 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13173 i).upper ≤ (0.532 : ℝ) ∧
    (cell13173 i).centre ≤ (0.1 : ℝ) ∧ (cell13173 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13173 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13173 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13173

/-! The local source numeric instances at 13173 have no network premises. -/
namespace BstLean.Part269.N13173
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13173)
open BstLean.Part268 (cell13173)

noncomputable def sourceNumerics13173 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13173 (cell13173 i)
      scalarRow13173.M scalarRow13173.H scalarRow13173.xi := by
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
    energy_allowance := scalarRow13173.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13173]
    centre_nonneg := (scalarRow13173.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13173])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13173
/-! Actual 13174 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13174 ≤ (1.035153498310 : ℝ) := by
  have hr : (114.778046681410 : ℝ) ≤ √(13174 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.778046681410 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13174 13174 (11 / 1000) ≤
    (0.008328133511 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13174) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.778046681410 : ℝ) ≤ √(13174 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13174)
  have hdiv : K / √(13174 : ℝ) ≤ K / 114.778046681410 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.778046681410 ≤ (0.008328133511 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13174.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13174 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13174 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13174 := gPlus_lower 13174
end BstLean.Part269.N13174

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13174
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035153498309 : ℝ) ≤ wn 13174 := by
  have hn : √(13174 : ℝ) ≤ 114.778046681411 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13174 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.778046681411 ≤ 2 / √(13174 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242664488 : ℝ) ≤ rhoBar 13174 BstLean.Part154.csC ∧
    rhoBar 13174 BstLean.Part154.csC ≤ 0.000242664864 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035153498309 : ℝ) / (1.295212 * 13174) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035153498310 : ℝ) / (1.29521 * 13174) := by gcongr
      _ ≤ (0.000242664864 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13174 BstLean.Part154.csC) ≤ 0.000970718343 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13174 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) ≤ 0.000185348745 ∧
    cc1 (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) ≤ 0.000117938702 ∧
    cc2 (rhoBar 13174 BstLean.Part154.csC) ≤ 0.000068464399 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13174 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13174 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13174 BstLean.Part154.csC * nuR (rhoBar 13174 BstLean.Part154.csC)) ≤ 0.000485344450 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242664864 : ℝ) * 0.000970718343 := by gcongr
      _ ≤ (0.000485344450 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13174 BstLean.Part154.csC) * nuR (rhoBar 13174 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970718343 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13174 BstLean.Part154.csC) * rhoBar 13174 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242664864 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242664864 / 2 + 0.399 * 0.000970718343 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185348745 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485344450 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117938702 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242664864 / 1.414213562 := by gcongr
      _ ≤ (0.000068464399 : ℝ) := by norm_num

end BstLean.Part269.N13174

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13174
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) ≤ 1.48360E-7 := by
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13174 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13174 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13174 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185348745 : ℝ) ^ 2 + 0.000117938702 ^ 2 + 3 * 0.000068464399 ^ 2 +
        2 * 0.797885 * 0.000185348745 * 0.000117938702 + 2 * 0.000185348745 * 0.000068464399 +
        4 * 0.797885 * 0.000117938702 * 0.000068464399 := by gcongr
    _ ≤ (1.48360E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13174 BstLean.Part154.csC Θ ≤ 0.002531484921 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13174 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13174 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13174 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035153498310 * 1.48360E-7 / (0.000242664488 : ℝ) := by gcongr
    _ ≤ 0.002531484921 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13174 BstLean.Part154.csC Θ ≤ 0.002807028072 + 0.000639663923 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13174 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13174 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035153498310 : ℝ) * ((2 * Θ * 0.000242664864 +
        (6863 / 10000) * 0.000242664864 * 13174 * 0.000970718343) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002807028072 + 0.000639663923 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13174 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13174 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13174 0.011 Θ ∧ gammaRatio 13174 0.011 Θ ≤ 0.000083421905 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13174 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035153498310 : ℝ) * 0.525 / ((1 - 0.011) * 13174) := by gcongr
      _ ≤ (0.000083421905 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13174 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13174 0.011 Θ) :=
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
    badAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13174 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13174 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13174 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13174 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13174 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13174 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13174 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13174 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13174 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13174 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035153498310 : ℝ) * 13174 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003123913230 + 0.003171148844 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13174

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13174
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13174 BstLean.Part154.csC) (piBar (rhoBar 13174 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13174 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13174 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13174 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13174 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13174 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13174 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13174 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13174 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13174 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13174 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051521327216 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13174) ≤ 0.010404756098 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13174 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035153498310)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010404756098 + 2 * 0.737676 / 13174) := by gcongr
    _ ≤ (0.051521327216 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13174 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13174

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13174
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524232723 : ℝ) ≤ plow 13174 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13174) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295366374)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329029584) : eMP 13174 0.011 xi bn ≤ 0.001144789087 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13174 : ℝ) * (1 - 0.011))) ≤ 0.000566089774 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001329029584 / (13174 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566089774 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566089774 : ℝ) + 3.141593 * 0.052295366374 / (13174 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144789087 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295366374)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329029584) : PiBarMP 13174 12 0.011 xi bn ≤ 0.158295025357 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13174 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036455858021 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.145021792454 : ℝ) ≤ √((13174 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.778046681410 : ℝ) ≤ √(13174 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13174) ≤ 0.121385654013 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036455858021 + 0.052295366374 * 1.772454 / (2 * (114.145021792454 : ℝ))) * (1 + 0.001144789087) +
        8 / (13174 * 114.778046681410) + 0.121385654013 := by gcongr
    _ ≤ (0.158295025357 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295366374)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329029584) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280203128797) :
    parallelOracle 13174 0.011 xi bn cd ≤ 0.159249924563 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13174 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13174 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524232723 : ℝ) ≤ plow 13174 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.778046681410 : ℝ) ≤ √(13174 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280203128797 : ℝ) / (2 * 0.560524232723 * 114.778046681410)) * 0.158295025357 +
        0.280203128797 ^ 2 / (2 * 0.560524232723 * 114.778046681410) := by gcongr
    _ ≤ (0.159249924563 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295366374) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001329029584)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280203128797) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13174 13174 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524232723 : ℝ) ≤ plow 13174 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.778046681410 : ℝ) ≤ √(13174 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13174 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13174 Θ 1.22 ≤ 0.011553607492 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.778046681410 := by gcongr <;> linarith
      _ ≤ (0.011553607492 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13174 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13174 13174 0.011 ≤ 0.008328133511 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13174 13174 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13174 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13174 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13174 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13174 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159249924563 + 0.011553607492 + (0.008328133511 : ℝ) *
        (1 + 2 * (0.280203128797 + 0.011553607492) / (0.560524232723 * 114.778046681410))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13174]

end BstLean.Part269.N13174

/-! The original eight local profiles supply actual 13174 moment certificates. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13174 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052295366374 ∧
    0 ≤ bN 13174 BstLean.Part154.csC (groupTheta g) ∧ bN 13174 BstLean.Part154.csC (groupTheta g) ≤ 0.001329029584 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13174 13174 0.011
      (momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13174 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13174 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13174 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228681801581 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13174 0.011
      (momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13174 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13174
/-! The actual computed-centre upper energy formula at 13174. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13174

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13174)
open BstLean.Part268 (cell13174)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084216080136
  | 2 => 0.085139141111
  | 3 => 0.086057592769
  | 4 => 0.086972205454
  | 5 => 0.087883929096
  | 6 => 0.088793922084
  | 7 => 0.089703583266
  | 8 => 0.090614587224
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13174 13174 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13174 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13174

/-! Actual upper energy certificates on all 43 source endpoints at 13174. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13174)
open BstLean.Part268 (cell13174)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13174 (gMinus 13174) (1 - (cell13174 i).lower) ≤ 1 ∧
    energyUpper 13174 (gMinus 13174) (BstLean.Part211.gPlus 13174)
      (finiteEnergy 13174 13174 0.011) (1 - (cell13174 i).lower) ≤
      (cell13174 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨10,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨11,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨12,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨13,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨14,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨15,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨16,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨17,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨18,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨19,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨20,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨21,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨22,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨23,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨24,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨25,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨26,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨27,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨28,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨29,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨30,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨31,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨32,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨33,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨34,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨35,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨36,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨37,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨38,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨39,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨40,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨41,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨42,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨43,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨44,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨45,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨46,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨47,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨48,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨49,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨50,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨51,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13174) (by norm_num)
        (q := 1 - (cell13174 ⟨52,by decide⟩).lower)
        (by norm_num [cell13174]) (by norm_num [cell13174])
      exact ⟨E.1,E.2.trans (by norm_num [cell13174])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13174

/-! Source-cell containment and simple scalar guards at 13174. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13174)
open BstLean.Part268 (cell13174)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13174 ⟨10,by decide⟩).lower ∧ (cell13174 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13174 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13174 ⟨11,by decide⟩).lower ∧ (cell13174 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13174 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13174 ⟨12,by decide⟩).lower ∧ (cell13174 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13174 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13174 ⟨13,by decide⟩).lower ∧ (cell13174 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13174 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13174 ⟨14,by decide⟩).lower ∧ (cell13174 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13174 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13174 ⟨15,by decide⟩).lower ∧ (cell13174 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13174 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13174 ⟨16,by decide⟩).lower ∧ (cell13174 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13174 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13174 ⟨17,by decide⟩).lower ∧ (cell13174 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13174 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13174 ⟨18,by decide⟩).lower ∧ (cell13174 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13174 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13174 ⟨19,by decide⟩).lower ∧ (cell13174 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13174 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13174 ⟨20,by decide⟩).lower ∧ (cell13174 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13174 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13174 ⟨21,by decide⟩).lower ∧ (cell13174 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13174 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13174 ⟨22,by decide⟩).lower ∧ (cell13174 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13174 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13174 ⟨23,by decide⟩).lower ∧ (cell13174 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13174 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13174 ⟨24,by decide⟩).lower ∧ (cell13174 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13174 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13174 ⟨25,by decide⟩).lower ∧ (cell13174 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13174 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13174 ⟨26,by decide⟩).lower ∧ (cell13174 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13174 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13174 ⟨27,by decide⟩).lower ∧ (cell13174 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13174 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13174 ⟨28,by decide⟩).lower ∧ (cell13174 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13174 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13174 ⟨29,by decide⟩).lower ∧ (cell13174 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13174 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13174 ⟨30,by decide⟩).lower ∧ (cell13174 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13174 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13174 ⟨31,by decide⟩).lower ∧ (cell13174 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13174 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13174 ⟨32,by decide⟩).lower ∧ (cell13174 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13174 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13174 ⟨33,by decide⟩).lower ∧ (cell13174 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13174 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13174 ⟨34,by decide⟩).lower ∧ (cell13174 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13174 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13174 ⟨35,by decide⟩).lower ∧ (cell13174 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13174 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13174 ⟨36,by decide⟩).lower ∧ (cell13174 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13174 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13174 ⟨37,by decide⟩).lower ∧ (cell13174 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13174 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13174 ⟨38,by decide⟩).lower ∧ (cell13174 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13174 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13174 ⟨39,by decide⟩).lower ∧ (cell13174 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13174 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13174 ⟨40,by decide⟩).lower ∧ (cell13174 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13174 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13174 ⟨41,by decide⟩).lower ∧ (cell13174 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13174 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13174 ⟨42,by decide⟩).lower ∧ (cell13174 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13174 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13174 ⟨43,by decide⟩).lower ∧ (cell13174 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13174 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13174 ⟨44,by decide⟩).lower ∧ (cell13174 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13174 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13174 ⟨45,by decide⟩).lower ∧ (cell13174 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13174 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13174 ⟨46,by decide⟩).lower ∧ (cell13174 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13174 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13174 ⟨47,by decide⟩).lower ∧ (cell13174 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13174 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13174 ⟨48,by decide⟩).lower ∧ (cell13174 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13174 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13174 ⟨49,by decide⟩).lower ∧ (cell13174 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13174 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13174 ⟨50,by decide⟩).lower ∧ (cell13174 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13174 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13174 ⟨51,by decide⟩).lower ∧ (cell13174 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13174 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13174 ⟨52,by decide⟩).lower ∧ (cell13174 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13174 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13174 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13174 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13174,cell13174,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13174 i).lower ∧
    (cell13174 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13174 i).upper ≤ (0.532 : ℝ) ∧
    (cell13174 i).centre ≤ (0.1 : ℝ) ∧ (cell13174 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13174 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13174 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13174

/-! The local source numeric instances at 13174 have no network premises. -/
namespace BstLean.Part269.N13174
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13174)
open BstLean.Part268 (cell13174)

noncomputable def sourceNumerics13174 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13174 (cell13174 i)
      scalarRow13174.M scalarRow13174.H scalarRow13174.xi := by
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
    energy_allowance := scalarRow13174.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13174]
    centre_nonneg := (scalarRow13174.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13174])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13174