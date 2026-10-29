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
import BstLean.Part269Direction19
import BstLean.Part269Shared19
import BstLean.Part269Finite
import BstLean.Part269Rows19
import BstLean.Part269Source
/-! Actual 12825 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12825 ≤ (1.035632753694 : ℝ) := by
  have hr : (113.247516529061 : ℝ) ≤ √(12825 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.247516529061 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12825 12825 (11 / 1000) ≤
    (0.008440688349 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12825) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.247516529061 : ℝ) ≤ √(12825 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12825)
  have hdiv : K / √(12825 : ℝ) ≤ K / 113.247516529061 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.247516529061 ≤ (0.008440688349 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12825.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12825 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12825 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12825 := gPlus_lower 12825
end BstLean.Part269.N12825

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12825
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035632753693 : ℝ) ≤ wn 12825 := by
  have hn : √(12825 : ℝ) ≤ 113.247516529062 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12825 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.247516529062 ≤ 2 / √(12825 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249383396 : ℝ) ≤ rhoBar 12825 BstLean.Part154.csC ∧
    rhoBar 12825 BstLean.Part154.csC ≤ 0.000249383782 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035632753693 : ℝ) / (1.295212 * 12825) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035632753694 : ℝ) / (1.29521 * 12825) := by gcongr
      _ ≤ (0.000249383782 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12825 BstLean.Part154.csC) ≤ 0.000997597321 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12825 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) ≤ 0.000190480927 ∧
    cc1 (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) ≤ 0.000121204297 ∧
    cc2 (rhoBar 12825 BstLean.Part154.csC) ≤ 0.000070360045 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12825 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12825 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12825 BstLean.Part154.csC * nuR (rhoBar 12825 BstLean.Part154.csC)) ≤ 0.000498783113 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249383782 : ℝ) * 0.000997597321 := by gcongr
      _ ≤ (0.000498783113 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12825 BstLean.Part154.csC) * nuR (rhoBar 12825 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997597321 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12825 BstLean.Part154.csC) * rhoBar 12825 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249383782 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249383782 / 2 + 0.399 * 0.000997597321 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190480927 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498783113 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121204297 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249383782 / 1.414213562 := by gcongr
      _ ≤ (0.000070360045 : ℝ) := by norm_num

end BstLean.Part269.N12825

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12825
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) ≤ 1.56689E-7 := by
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12825 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12825 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12825 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190480927 : ℝ) ^ 2 + 0.000121204297 ^ 2 + 3 * 0.000070360045 ^ 2 +
        2 * 0.797885 * 0.000190480927 * 0.000121204297 + 2 * 0.000190480927 * 0.000070360045 +
        4 * 0.797885 * 0.000121204297 * 0.000070360045 := by gcongr
    _ ≤ (1.56689E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12825 BstLean.Part154.csC Θ ≤ 0.002602775697 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12825 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12825 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12825 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035632753694 * 1.56689E-7 / (0.000249383396 : ℝ) := by gcongr
    _ ≤ 0.002602775697 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12825 BstLean.Part154.csC Θ ≤ 0.002887425849 + 0.000657679325 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12825 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12825 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035632753694 : ℝ) * ((2 * Θ * 0.000249383782 +
        (6863 / 10000) * 0.000249383782 * 12825 * 0.000997597321) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002887425849 + 0.000657679325 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12825 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12825 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12825 0.011 Θ ∧ gammaRatio 12825 0.011 Θ ≤ 0.000085731696 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12825 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035632753694 : ℝ) * 0.525 / ((1 - 0.011) * 12825) := by gcongr
      _ ≤ (0.000085731696 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12825 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12825 0.011 Θ) :=
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
    badAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12825 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12825 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12825 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12825 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12825 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12825 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12825 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12825 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12825 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12825 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035632753694 : ℝ) * 12825 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003397088065 + 0.003260455022 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12825

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12825
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12825 BstLean.Part154.csC) (piBar (rhoBar 12825 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12825 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12825 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12825 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12825 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12825 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12825 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12825 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12825 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12825 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12825 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052225148355 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12825) ≤ 0.010545375455 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12825 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035632753694)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010545375455 + 2 * 0.737676 / 12825) := by gcongr
    _ ≤ (0.052225148355 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12825 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12825

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12825
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509166066 : ℝ) ≤ plow 12825 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12825) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615426952)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366457241) : eMP 12825 0.011 xi bn ≤ 0.001176558095 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12825 : ℝ) * (1 - 0.011))) ≤ 0.000581763073 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366457241 / (12825 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581763073 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581763073 : ℝ) + 3.141593 * 0.052615426952 / (12825 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176558095 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615426952)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366457241) : PiBarMP 12825 12 0.011 xi bn ≤ 0.160455309714 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12825 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036965622422 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.622932833415 : ℝ) ≤ √((12825 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.247516529061 : ℝ) ≤ √(12825 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12825) ≤ 0.123026170373 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036965622422 + 0.052615426952 * 1.772454 / (2 * (112.622932833415 : ℝ))) * (1 + 0.001176558095) +
        8 / (12825 * 113.247516529061) + 0.123026170373 := by gcongr
    _ ≤ (0.160455309714 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615426952)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366457241) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281605677067) :
    parallelOracle 12825 0.011 xi bn cd ≤ 0.161435887822 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12825 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12825 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509166066 : ℝ) ≤ plow 12825 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.247516529061 : ℝ) ≤ √(12825 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281605677067 : ℝ) / (2 * 0.560509166066 * 113.247516529061)) * 0.160455309714 +
        0.281605677067 ^ 2 / (2 * 0.560509166066 * 113.247516529061) := by gcongr
    _ ≤ (0.161435887822 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615426952) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366457241)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281605677067) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12825 12825 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509166066 : ℝ) ≤ plow 12825 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.247516529061 : ℝ) ≤ √(12825 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12825 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12825 Θ 1.22 ≤ 0.011709753474 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.247516529061 := by gcongr <;> linarith
      _ ≤ (0.011709753474 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12825 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12825 12825 0.011 ≤ 0.008440688349 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12825 12825 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12825 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12825 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12825 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12825 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161435887822 + 0.011709753474 + (0.008440688349 : ℝ) *
        (1 + 2 * (0.281605677067 + 0.011709753474) / (0.560509166066 * 113.247516529061))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12825]

end BstLean.Part269.N12825

/-! The original eight local profiles supply actual 12825 moment certificates. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12825 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052615426952 ∧
    0 ≤ bN 12825 BstLean.Part154.csC (groupTheta g) ∧ bN 12825 BstLean.Part154.csC (groupTheta g) ≤ 0.001366457241 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12825 12825 0.011
      (momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12825 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12825 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12825 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229380528712 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12825 0.011
      (momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12825 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12825
/-! The actual computed-centre upper energy formula at 12825. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12825

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12825)
open BstLean.Part268 (cell12825)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085133844242
  | 2 => 0.086070225745
  | 3 => 0.087003847348
  | 4 => 0.087935917880
  | 5 => 0.088867906050
  | 6 => 0.089801579887
  | 7 => 0.090739050046
  | 8 => 0.091682817043
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12825 12825 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12825 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12825

/-! Actual upper energy certificates on all 43 source endpoints at 12825. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12825)
open BstLean.Part268 (cell12825)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12825 (gMinus 12825) (1 - (cell12825 i).lower) ≤ 1 ∧
    energyUpper 12825 (gMinus 12825) (BstLean.Part211.gPlus 12825)
      (finiteEnergy 12825 12825 0.011) (1 - (cell12825 i).lower) ≤
      (cell12825 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨10,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨11,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨12,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨13,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨14,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨15,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨16,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨17,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨18,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨19,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨20,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨21,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨22,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨23,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨24,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨25,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨26,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨27,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨28,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨29,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨30,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨31,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨32,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨33,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨34,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨35,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨36,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨37,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨38,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨39,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨40,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨41,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨42,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨43,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨44,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨45,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨46,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨47,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨48,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨49,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨50,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨51,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12825) (by norm_num)
        (q := 1 - (cell12825 ⟨52,by decide⟩).lower)
        (by norm_num [cell12825]) (by norm_num [cell12825])
      exact ⟨E.1,E.2.trans (by norm_num [cell12825])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12825

/-! Source-cell containment and simple scalar guards at 12825. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12825)
open BstLean.Part268 (cell12825)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12825 ⟨10,by decide⟩).lower ∧ (cell12825 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12825 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12825 ⟨11,by decide⟩).lower ∧ (cell12825 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12825 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12825 ⟨12,by decide⟩).lower ∧ (cell12825 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12825 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12825 ⟨13,by decide⟩).lower ∧ (cell12825 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12825 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12825 ⟨14,by decide⟩).lower ∧ (cell12825 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12825 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12825 ⟨15,by decide⟩).lower ∧ (cell12825 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12825 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12825 ⟨16,by decide⟩).lower ∧ (cell12825 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12825 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12825 ⟨17,by decide⟩).lower ∧ (cell12825 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12825 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12825 ⟨18,by decide⟩).lower ∧ (cell12825 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12825 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12825 ⟨19,by decide⟩).lower ∧ (cell12825 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12825 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12825 ⟨20,by decide⟩).lower ∧ (cell12825 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12825 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12825 ⟨21,by decide⟩).lower ∧ (cell12825 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12825 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12825 ⟨22,by decide⟩).lower ∧ (cell12825 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12825 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12825 ⟨23,by decide⟩).lower ∧ (cell12825 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12825 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12825 ⟨24,by decide⟩).lower ∧ (cell12825 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12825 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12825 ⟨25,by decide⟩).lower ∧ (cell12825 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12825 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12825 ⟨26,by decide⟩).lower ∧ (cell12825 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12825 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12825 ⟨27,by decide⟩).lower ∧ (cell12825 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12825 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12825 ⟨28,by decide⟩).lower ∧ (cell12825 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12825 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12825 ⟨29,by decide⟩).lower ∧ (cell12825 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12825 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12825 ⟨30,by decide⟩).lower ∧ (cell12825 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12825 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12825 ⟨31,by decide⟩).lower ∧ (cell12825 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12825 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12825 ⟨32,by decide⟩).lower ∧ (cell12825 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12825 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12825 ⟨33,by decide⟩).lower ∧ (cell12825 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12825 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12825 ⟨34,by decide⟩).lower ∧ (cell12825 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12825 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12825 ⟨35,by decide⟩).lower ∧ (cell12825 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12825 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12825 ⟨36,by decide⟩).lower ∧ (cell12825 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12825 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12825 ⟨37,by decide⟩).lower ∧ (cell12825 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12825 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12825 ⟨38,by decide⟩).lower ∧ (cell12825 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12825 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12825 ⟨39,by decide⟩).lower ∧ (cell12825 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12825 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12825 ⟨40,by decide⟩).lower ∧ (cell12825 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12825 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12825 ⟨41,by decide⟩).lower ∧ (cell12825 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12825 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12825 ⟨42,by decide⟩).lower ∧ (cell12825 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12825 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12825 ⟨43,by decide⟩).lower ∧ (cell12825 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12825 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12825 ⟨44,by decide⟩).lower ∧ (cell12825 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12825 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12825 ⟨45,by decide⟩).lower ∧ (cell12825 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12825 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12825 ⟨46,by decide⟩).lower ∧ (cell12825 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12825 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12825 ⟨47,by decide⟩).lower ∧ (cell12825 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12825 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12825 ⟨48,by decide⟩).lower ∧ (cell12825 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12825 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12825 ⟨49,by decide⟩).lower ∧ (cell12825 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12825 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12825 ⟨50,by decide⟩).lower ∧ (cell12825 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12825 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12825 ⟨51,by decide⟩).lower ∧ (cell12825 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12825 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12825 ⟨52,by decide⟩).lower ∧ (cell12825 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12825 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12825 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12825 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12825,cell12825,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12825 i).lower ∧
    (cell12825 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12825 i).upper ≤ (0.532 : ℝ) ∧
    (cell12825 i).centre ≤ (0.1 : ℝ) ∧ (cell12825 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12825 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12825 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12825

/-! The local source numeric instances at 12825 have no network premises. -/
namespace BstLean.Part269.N12825
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12825)
open BstLean.Part268 (cell12825)

noncomputable def sourceNumerics12825 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12825 (cell12825 i)
      scalarRow12825.M scalarRow12825.H scalarRow12825.xi := by
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
    energy_allowance := scalarRow12825.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12825]
    centre_nonneg := (scalarRow12825.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12825])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12825
/-! Actual 12826 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12826 ≤ (1.035631352426 : ℝ) := by
  have hr : (113.251931550857 : ℝ) ≤ √(12826 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.251931550857 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12826 12826 (11 / 1000) ≤
    (0.008440359294 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12826) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.251931550857 : ℝ) ≤ √(12826 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12826)
  have hdiv : K / √(12826 : ℝ) ≤ K / 113.251931550857 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.251931550857 ≤ (0.008440359294 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12826.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12826 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12826 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12826 := gPlus_lower 12826
end BstLean.Part269.N12826

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12826
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035631352425 : ℝ) ≤ wn 12826 := by
  have hn : √(12826 : ℝ) ≤ 113.251931550858 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12826 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.251931550858 ≤ 2 / √(12826 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249363615 : ℝ) ≤ rhoBar 12826 BstLean.Part154.csC ∧
    rhoBar 12826 BstLean.Part154.csC ≤ 0.000249364001 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035631352425 : ℝ) / (1.295212 * 12826) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035631352426 : ℝ) / (1.29521 * 12826) := by gcongr
      _ ≤ (0.000249364001 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12826 BstLean.Part154.csC) ≤ 0.000997518187 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12826 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) ≤ 0.000190465818 ∧
    cc1 (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) ≤ 0.000121194683 ∧
    cc2 (rhoBar 12826 BstLean.Part154.csC) ≤ 0.000070354464 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12826 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12826 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12826 BstLean.Part154.csC * nuR (rhoBar 12826 BstLean.Part154.csC)) ≤ 0.000498743548 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249364001 : ℝ) * 0.000997518187 := by gcongr
      _ ≤ (0.000498743548 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12826 BstLean.Part154.csC) * nuR (rhoBar 12826 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997518187 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12826 BstLean.Part154.csC) * rhoBar 12826 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249364001 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249364001 / 2 + 0.399 * 0.000997518187 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190465818 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498743548 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121194683 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249364001 / 1.414213562 := by gcongr
      _ ≤ (0.000070354464 : ℝ) := by norm_num

end BstLean.Part269.N12826

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12826
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) ≤ 1.56664E-7 := by
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12826 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12826 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12826 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190465818 : ℝ) ^ 2 + 0.000121194683 ^ 2 + 3 * 0.000070354464 ^ 2 +
        2 * 0.797885 * 0.000190465818 * 0.000121194683 + 2 * 0.000190465818 * 0.000070354464 +
        4 * 0.797885 * 0.000121194683 * 0.000070354464 := by gcongr
    _ ≤ (1.56664E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12826 BstLean.Part154.csC Θ ≤ 0.002602563333 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12826 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12826 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12826 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035631352426 * 1.56664E-7 / (0.000249363615 : ℝ) := by gcongr
    _ ≤ 0.002602563333 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12826 BstLean.Part154.csC Θ ≤ 0.002887188993 + 0.000657626268 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12826 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12826 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035631352426 : ℝ) * ((2 * Θ * 0.000249364001 +
        (6863 / 10000) * 0.000249364001 * 12826 * 0.000997518187) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002887188993 + 0.000657626268 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12826 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12826 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12826 0.011 Θ ∧ gammaRatio 12826 0.011 Θ ≤ 0.000085724895 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12826 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035631352426 : ℝ) * 0.525 / ((1 - 0.011) * 12826) := by gcongr
      _ ≤ (0.000085724895 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12826 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12826 0.011 Θ) :=
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
    badAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12826 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12826 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12826 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12826 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12826 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12826 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12826 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12826 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12826 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12826 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035631352426 : ℝ) * 12826 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396851209 + 0.003260189601 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12826

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12826
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12826 BstLean.Part154.csC) (piBar (rhoBar 12826 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12826 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12826 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12826 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12826 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12826 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12826 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12826 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12826 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12826 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12826 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052223090435 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12826) ≤ 0.010544964353 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12826 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035631352426)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010544964353 + 2 * 0.737676 / 12826) := by gcongr
    _ ≤ (0.052223090435 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12826 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12826

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12826
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509210408 : ℝ) ≤ plow 12826 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12826) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615050750)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366345750) : eMP 12826 0.011 xi bn ≤ 0.001176464160 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12826 : ℝ) * (1 - 0.011))) ≤ 0.000581716660 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366345750 / (12826 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581716660 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581716660 : ℝ) + 3.141593 * 0.052615050750 / (12826 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176464160 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615050750)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366345750) : PiBarMP 12826 12 0.011 xi bn ≤ 0.160448980532 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12826 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036964114355 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.627323505444 : ℝ) ≤ √((12826 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.251931550857 : ℝ) ≤ √(12826 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12826) ≤ 0.123021374311 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036964114355 + 0.052615050750 * 1.772454 / (2 * (112.627323505444 : ℝ))) * (1 + 0.001176464160) +
        8 / (12826 * 113.251931550857) + 0.123021374311 := by gcongr
    _ ≤ (0.160448980532 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615050750)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366345750) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281602799107) :
    parallelOracle 12826 0.011 xi bn cd ≤ 0.161429489892 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12826 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12826 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509210408 : ℝ) ≤ plow 12826 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.251931550857 : ℝ) ≤ √(12826 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281602799107 : ℝ) / (2 * 0.560509210408 * 113.251931550857)) * 0.160448980532 +
        0.281602799107 ^ 2 / (2 * 0.560509210408 * 113.251931550857) := by gcongr
    _ ≤ (0.161429489892 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615050750) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366345750)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281602799107) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12826 12826 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509210408 : ℝ) ≤ plow 12826 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.251931550857 : ℝ) ≤ √(12826 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12826 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12826 Θ 1.22 ≤ 0.011709296980 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.251931550857 := by gcongr <;> linarith
      _ ≤ (0.011709296980 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12826 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12826 12826 0.011 ≤ 0.008440359294 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12826 12826 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12826 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12826 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12826 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12826 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161429489892 + 0.011709296980 + (0.008440359294 : ℝ) *
        (1 + 2 * (0.281602799107 + 0.011709296980) / (0.560509210408 * 113.251931550857))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12826]

end BstLean.Part269.N12826

/-! The original eight local profiles supply actual 12826 moment certificates. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12826 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052615050750 ∧
    0 ≤ bN 12826 BstLean.Part154.csC (groupTheta g) ∧ bN 12826 BstLean.Part154.csC (groupTheta g) ≤ 0.001366345750 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12826 12826 0.011
      (momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12826 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12826 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12826 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229379708672 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12826 0.011
      (momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12826 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12826
/-! The actual computed-centre upper energy formula at 12826. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12826

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12826)
open BstLean.Part268 (cell12826)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085131055783
  | 2 => 0.086067388862
  | 3 => 0.087000955436
  | 4 => 0.087932962782
  | 5 => 0.088864877779
  | 6 => 0.089798466310
  | 7 => 0.090735836529
  | 8 => 0.091679486060
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12826 12826 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12826 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12826

/-! Actual upper energy certificates on all 43 source endpoints at 12826. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12826)
open BstLean.Part268 (cell12826)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12826 (gMinus 12826) (1 - (cell12826 i).lower) ≤ 1 ∧
    energyUpper 12826 (gMinus 12826) (BstLean.Part211.gPlus 12826)
      (finiteEnergy 12826 12826 0.011) (1 - (cell12826 i).lower) ≤
      (cell12826 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨10,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨11,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨12,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨13,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨14,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨15,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨16,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨17,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨18,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨19,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨20,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨21,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨22,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨23,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨24,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨25,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨26,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨27,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨28,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨29,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨30,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨31,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨32,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨33,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨34,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨35,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨36,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨37,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨38,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨39,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨40,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨41,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨42,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨43,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨44,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨45,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨46,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨47,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨48,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨49,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨50,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨51,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12826) (by norm_num)
        (q := 1 - (cell12826 ⟨52,by decide⟩).lower)
        (by norm_num [cell12826]) (by norm_num [cell12826])
      exact ⟨E.1,E.2.trans (by norm_num [cell12826])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12826

/-! Source-cell containment and simple scalar guards at 12826. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12826)
open BstLean.Part268 (cell12826)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12826 ⟨10,by decide⟩).lower ∧ (cell12826 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12826 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12826 ⟨11,by decide⟩).lower ∧ (cell12826 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12826 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12826 ⟨12,by decide⟩).lower ∧ (cell12826 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12826 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12826 ⟨13,by decide⟩).lower ∧ (cell12826 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12826 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12826 ⟨14,by decide⟩).lower ∧ (cell12826 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12826 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12826 ⟨15,by decide⟩).lower ∧ (cell12826 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12826 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12826 ⟨16,by decide⟩).lower ∧ (cell12826 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12826 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12826 ⟨17,by decide⟩).lower ∧ (cell12826 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12826 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12826 ⟨18,by decide⟩).lower ∧ (cell12826 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12826 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12826 ⟨19,by decide⟩).lower ∧ (cell12826 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12826 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12826 ⟨20,by decide⟩).lower ∧ (cell12826 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12826 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12826 ⟨21,by decide⟩).lower ∧ (cell12826 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12826 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12826 ⟨22,by decide⟩).lower ∧ (cell12826 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12826 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12826 ⟨23,by decide⟩).lower ∧ (cell12826 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12826 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12826 ⟨24,by decide⟩).lower ∧ (cell12826 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12826 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12826 ⟨25,by decide⟩).lower ∧ (cell12826 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12826 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12826 ⟨26,by decide⟩).lower ∧ (cell12826 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12826 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12826 ⟨27,by decide⟩).lower ∧ (cell12826 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12826 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12826 ⟨28,by decide⟩).lower ∧ (cell12826 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12826 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12826 ⟨29,by decide⟩).lower ∧ (cell12826 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12826 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12826 ⟨30,by decide⟩).lower ∧ (cell12826 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12826 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12826 ⟨31,by decide⟩).lower ∧ (cell12826 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12826 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12826 ⟨32,by decide⟩).lower ∧ (cell12826 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12826 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12826 ⟨33,by decide⟩).lower ∧ (cell12826 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12826 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12826 ⟨34,by decide⟩).lower ∧ (cell12826 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12826 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12826 ⟨35,by decide⟩).lower ∧ (cell12826 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12826 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12826 ⟨36,by decide⟩).lower ∧ (cell12826 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12826 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12826 ⟨37,by decide⟩).lower ∧ (cell12826 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12826 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12826 ⟨38,by decide⟩).lower ∧ (cell12826 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12826 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12826 ⟨39,by decide⟩).lower ∧ (cell12826 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12826 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12826 ⟨40,by decide⟩).lower ∧ (cell12826 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12826 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12826 ⟨41,by decide⟩).lower ∧ (cell12826 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12826 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12826 ⟨42,by decide⟩).lower ∧ (cell12826 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12826 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12826 ⟨43,by decide⟩).lower ∧ (cell12826 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12826 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12826 ⟨44,by decide⟩).lower ∧ (cell12826 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12826 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12826 ⟨45,by decide⟩).lower ∧ (cell12826 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12826 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12826 ⟨46,by decide⟩).lower ∧ (cell12826 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12826 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12826 ⟨47,by decide⟩).lower ∧ (cell12826 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12826 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12826 ⟨48,by decide⟩).lower ∧ (cell12826 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12826 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12826 ⟨49,by decide⟩).lower ∧ (cell12826 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12826 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12826 ⟨50,by decide⟩).lower ∧ (cell12826 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12826 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12826 ⟨51,by decide⟩).lower ∧ (cell12826 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12826 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12826 ⟨52,by decide⟩).lower ∧ (cell12826 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12826 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12826 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12826 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12826,cell12826,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12826 i).lower ∧
    (cell12826 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12826 i).upper ≤ (0.532 : ℝ) ∧
    (cell12826 i).centre ≤ (0.1 : ℝ) ∧ (cell12826 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12826 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12826 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12826

/-! The local source numeric instances at 12826 have no network premises. -/
namespace BstLean.Part269.N12826
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12826)
open BstLean.Part268 (cell12826)

noncomputable def sourceNumerics12826 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12826 (cell12826 i)
      scalarRow12826.M scalarRow12826.H scalarRow12826.xi := by
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
    energy_allowance := scalarRow12826.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12826]
    centre_nonneg := (scalarRow12826.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12826])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12826
/-! Actual 12827 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12827 ≤ (1.035629951322 : ℝ) := by
  have hr : (113.256346400543 : ℝ) ≤ √(12827 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.256346400543 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12827 12827 (11 / 1000) ≤
    (0.008440030277 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12827) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.256346400543 : ℝ) ≤ √(12827 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12827)
  have hdiv : K / √(12827 : ℝ) ≤ K / 113.256346400543 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.256346400543 ≤ (0.008440030277 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12827.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12827 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12827 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12827 := gPlus_lower 12827
end BstLean.Part269.N12827

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12827
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035629951321 : ℝ) ≤ wn 12827 := by
  have hn : √(12827 : ℝ) ≤ 113.256346400544 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12827 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.256346400544 ≤ 2 / √(12827 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249343837 : ℝ) ≤ rhoBar 12827 BstLean.Part154.csC ∧
    rhoBar 12827 BstLean.Part154.csC ≤ 0.000249344223 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035629951321 : ℝ) / (1.295212 * 12827) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035629951322 : ℝ) / (1.29521 * 12827) := by gcongr
      _ ≤ (0.000249344223 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12827 BstLean.Part154.csC) ≤ 0.000997439065 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12827 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) ≤ 0.000190450710 ∧
    cc1 (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) ≤ 0.000121185070 ∧
    cc2 (rhoBar 12827 BstLean.Part154.csC) ≤ 0.000070348884 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12827 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12827 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12827 BstLean.Part154.csC * nuR (rhoBar 12827 BstLean.Part154.csC)) ≤ 0.000498703990 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249344223 : ℝ) * 0.000997439065 := by gcongr
      _ ≤ (0.000498703990 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12827 BstLean.Part154.csC) * nuR (rhoBar 12827 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997439065 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12827 BstLean.Part154.csC) * rhoBar 12827 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249344223 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249344223 / 2 + 0.399 * 0.000997439065 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190450710 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498703990 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121185070 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249344223 / 1.414213562 := by gcongr
      _ ≤ (0.000070348884 : ℝ) := by norm_num

end BstLean.Part269.N12827

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12827
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) ≤ 1.56639E-7 := by
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12827 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12827 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12827 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190450710 : ℝ) ^ 2 + 0.000121185070 ^ 2 + 3 * 0.000070348884 ^ 2 +
        2 * 0.797885 * 0.000190450710 * 0.000121185070 + 2 * 0.000190450710 * 0.000070348884 +
        4 * 0.797885 * 0.000121185070 * 0.000070348884 := by gcongr
    _ ≤ (1.56639E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12827 BstLean.Part154.csC Θ ≤ 0.002602350905 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12827 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12827 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12827 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035629951322 * 1.56639E-7 / (0.000249343837 : ℝ) := by gcongr
    _ ≤ 0.002602350905 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12827 BstLean.Part154.csC Θ ≤ 0.002886952171 + 0.000657573219 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12827 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12827 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035629951322 : ℝ) * ((2 * Θ * 0.000249344223 +
        (6863 / 10000) * 0.000249344223 * 12827 * 0.000997439065) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002886952171 + 0.000657573219 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12827 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12827 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12827 0.011 Θ ∧ gammaRatio 12827 0.011 Θ ≤ 0.000085718096 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12827 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035629951322 : ℝ) * 0.525 / ((1 - 0.011) * 12827) := by gcongr
      _ ≤ (0.000085718096 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12827 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12827 0.011 Θ) :=
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
    badAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12827 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12827 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12827 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12827 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12827 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12827 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12827 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12827 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12827 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12827 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035629951322 : ℝ) * 12827 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396614387 + 0.003259924124 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12827

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12827
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12827 BstLean.Part154.csC) (piBar (rhoBar 12827 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12827 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12827 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12827 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12827 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12827 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12827 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12827 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12827 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12827 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12827 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052221032757 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12827) ≤ 0.010544553299 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12827 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035629951322)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010544553299 + 2 * 0.737676 / 12827) := by gcongr
    _ ≤ (0.052221032757 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12827 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12827

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12827
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509254743 : ℝ) ≤ plow 12827 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12827) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614674553)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366234226) : eMP 12827 0.011 xi bn ≤ 0.001176370219 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12827 : ℝ) * (1 - 0.011))) ≤ 0.000581670244 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366234226 / (12827 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581670244 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581670244 : ℝ) + 3.141593 * 0.052614674553 / (12827 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176370219 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614674553)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366234226) : PiBarMP 12827 12 0.011 xi bn ≤ 0.160442651406 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12827 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036962605780 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.631714006313 : ℝ) ≤ √((12827 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.256346400543 : ℝ) ≤ √(12827 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12827) ≤ 0.123016578811 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036962605780 + 0.052614674553 * 1.772454 / (2 * (112.631714006313 : ℝ))) * (1 + 0.001176370219) +
        8 / (12827 * 113.256346400543) + 0.123016578811 := by gcongr
    _ ≤ (0.160442651406 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614674553)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366234226) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281599921396) :
    parallelOracle 12827 0.011 xi bn cd ≤ 0.161423092028 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12827 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12827 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509254743 : ℝ) ≤ plow 12827 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.256346400543 : ℝ) ≤ √(12827 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281599921396 : ℝ) / (2 * 0.560509254743 * 113.256346400543)) * 0.160442651406 +
        0.281599921396 ^ 2 / (2 * 0.560509254743 * 113.256346400543) := by gcongr
    _ ≤ (0.161423092028 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614674553) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366234226)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281599921396) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12827 12827 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509254743 : ℝ) ≤ plow 12827 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.256346400543 : ℝ) ≤ √(12827 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12827 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12827 Θ 1.22 ≤ 0.011708840539 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.256346400543 := by gcongr <;> linarith
      _ ≤ (0.011708840539 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12827 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12827 12827 0.011 ≤ 0.008440030277 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12827 12827 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12827 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12827 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12827 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12827 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161423092028 + 0.011708840539 + (0.008440030277 : ℝ) *
        (1 + 2 * (0.281599921396 + 0.011708840539) / (0.560509254743 * 113.256346400543))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12827]

end BstLean.Part269.N12827

/-! The original eight local profiles supply actual 12827 moment certificates. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12827 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052614674553 ∧
    0 ≤ bN 12827 BstLean.Part154.csC (groupTheta g) ∧ bN 12827 BstLean.Part154.csC (groupTheta g) ≤ 0.001366234226 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12827 12827 0.011
      (momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12827 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12827 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12827 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229378888639 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12827 0.011
      (momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12827 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12827
/-! The actual computed-centre upper energy formula at 12827. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12827

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12827)
open BstLean.Part268 (cell12827)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085128268281
  | 2 => 0.086064552973
  | 3 => 0.086998064565
  | 4 => 0.087930008783
  | 5 => 0.088861850677
  | 6 => 0.089795353987
  | 7 => 0.090732624369
  | 8 => 0.091676156560
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12827 12827 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12827 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12827

/-! Actual upper energy certificates on all 43 source endpoints at 12827. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12827)
open BstLean.Part268 (cell12827)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12827 (gMinus 12827) (1 - (cell12827 i).lower) ≤ 1 ∧
    energyUpper 12827 (gMinus 12827) (BstLean.Part211.gPlus 12827)
      (finiteEnergy 12827 12827 0.011) (1 - (cell12827 i).lower) ≤
      (cell12827 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨10,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨11,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨12,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨13,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨14,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨15,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨16,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨17,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨18,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨19,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨20,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨21,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨22,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨23,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨24,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨25,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨26,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨27,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨28,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨29,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨30,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨31,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨32,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨33,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨34,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨35,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨36,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨37,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨38,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨39,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨40,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨41,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨42,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨43,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨44,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨45,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨46,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨47,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨48,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨49,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨50,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨51,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12827) (by norm_num)
        (q := 1 - (cell12827 ⟨52,by decide⟩).lower)
        (by norm_num [cell12827]) (by norm_num [cell12827])
      exact ⟨E.1,E.2.trans (by norm_num [cell12827])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12827

/-! Source-cell containment and simple scalar guards at 12827. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12827)
open BstLean.Part268 (cell12827)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12827 ⟨10,by decide⟩).lower ∧ (cell12827 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12827 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12827 ⟨11,by decide⟩).lower ∧ (cell12827 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12827 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12827 ⟨12,by decide⟩).lower ∧ (cell12827 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12827 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12827 ⟨13,by decide⟩).lower ∧ (cell12827 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12827 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12827 ⟨14,by decide⟩).lower ∧ (cell12827 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12827 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12827 ⟨15,by decide⟩).lower ∧ (cell12827 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12827 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12827 ⟨16,by decide⟩).lower ∧ (cell12827 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12827 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12827 ⟨17,by decide⟩).lower ∧ (cell12827 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12827 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12827 ⟨18,by decide⟩).lower ∧ (cell12827 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12827 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12827 ⟨19,by decide⟩).lower ∧ (cell12827 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12827 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12827 ⟨20,by decide⟩).lower ∧ (cell12827 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12827 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12827 ⟨21,by decide⟩).lower ∧ (cell12827 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12827 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12827 ⟨22,by decide⟩).lower ∧ (cell12827 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12827 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12827 ⟨23,by decide⟩).lower ∧ (cell12827 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12827 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12827 ⟨24,by decide⟩).lower ∧ (cell12827 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12827 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12827 ⟨25,by decide⟩).lower ∧ (cell12827 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12827 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12827 ⟨26,by decide⟩).lower ∧ (cell12827 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12827 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12827 ⟨27,by decide⟩).lower ∧ (cell12827 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12827 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12827 ⟨28,by decide⟩).lower ∧ (cell12827 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12827 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12827 ⟨29,by decide⟩).lower ∧ (cell12827 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12827 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12827 ⟨30,by decide⟩).lower ∧ (cell12827 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12827 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12827 ⟨31,by decide⟩).lower ∧ (cell12827 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12827 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12827 ⟨32,by decide⟩).lower ∧ (cell12827 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12827 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12827 ⟨33,by decide⟩).lower ∧ (cell12827 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12827 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12827 ⟨34,by decide⟩).lower ∧ (cell12827 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12827 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12827 ⟨35,by decide⟩).lower ∧ (cell12827 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12827 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12827 ⟨36,by decide⟩).lower ∧ (cell12827 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12827 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12827 ⟨37,by decide⟩).lower ∧ (cell12827 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12827 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12827 ⟨38,by decide⟩).lower ∧ (cell12827 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12827 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12827 ⟨39,by decide⟩).lower ∧ (cell12827 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12827 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12827 ⟨40,by decide⟩).lower ∧ (cell12827 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12827 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12827 ⟨41,by decide⟩).lower ∧ (cell12827 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12827 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12827 ⟨42,by decide⟩).lower ∧ (cell12827 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12827 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12827 ⟨43,by decide⟩).lower ∧ (cell12827 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12827 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12827 ⟨44,by decide⟩).lower ∧ (cell12827 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12827 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12827 ⟨45,by decide⟩).lower ∧ (cell12827 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12827 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12827 ⟨46,by decide⟩).lower ∧ (cell12827 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12827 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12827 ⟨47,by decide⟩).lower ∧ (cell12827 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12827 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12827 ⟨48,by decide⟩).lower ∧ (cell12827 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12827 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12827 ⟨49,by decide⟩).lower ∧ (cell12827 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12827 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12827 ⟨50,by decide⟩).lower ∧ (cell12827 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12827 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12827 ⟨51,by decide⟩).lower ∧ (cell12827 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12827 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12827 ⟨52,by decide⟩).lower ∧ (cell12827 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12827 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12827 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12827 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12827,cell12827,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12827 i).lower ∧
    (cell12827 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12827 i).upper ≤ (0.532 : ℝ) ∧
    (cell12827 i).centre ≤ (0.1 : ℝ) ∧ (cell12827 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12827 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12827 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12827

/-! The local source numeric instances at 12827 have no network premises. -/
namespace BstLean.Part269.N12827
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12827)
open BstLean.Part268 (cell12827)

noncomputable def sourceNumerics12827 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12827 (cell12827 i)
      scalarRow12827.M scalarRow12827.H scalarRow12827.xi := by
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
    energy_allowance := scalarRow12827.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12827]
    centre_nonneg := (scalarRow12827.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12827])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12827
/-! Actual 12828 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12828 ≤ (1.035628550383 : ℝ) := by
  have hr : (113.260761078142 : ℝ) ≤ √(12828 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.260761078142 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12828 12828 (11 / 1000) ≤
    (0.008439701299 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12828) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.260761078142 : ℝ) ≤ √(12828 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12828)
  have hdiv : K / √(12828 : ℝ) ≤ K / 113.260761078142 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.260761078142 ≤ (0.008439701299 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12828.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12828 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12828 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12828 := gPlus_lower 12828
end BstLean.Part269.N12828

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12828
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035628550382 : ℝ) ≤ wn 12828 := by
  have hn : √(12828 : ℝ) ≤ 113.260761078143 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12828 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.260761078143 ≤ 2 / √(12828 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249324062 : ℝ) ≤ rhoBar 12828 BstLean.Part154.csC ∧
    rhoBar 12828 BstLean.Part154.csC ≤ 0.000249324448 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035628550382 : ℝ) / (1.295212 * 12828) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035628550383 : ℝ) / (1.29521 * 12828) := by gcongr
      _ ≤ (0.000249324448 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12828 BstLean.Part154.csC) ≤ 0.000997359955 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12828 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) ≤ 0.000190435605 ∧
    cc1 (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) ≤ 0.000121175459 ∧
    cc2 (rhoBar 12828 BstLean.Part154.csC) ≤ 0.000070343305 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12828 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12828 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12828 BstLean.Part154.csC * nuR (rhoBar 12828 BstLean.Part154.csC)) ≤ 0.000498664437 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249324448 : ℝ) * 0.000997359955 := by gcongr
      _ ≤ (0.000498664437 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12828 BstLean.Part154.csC) * nuR (rhoBar 12828 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997359955 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12828 BstLean.Part154.csC) * rhoBar 12828 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249324448 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249324448 / 2 + 0.399 * 0.000997359955 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190435605 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498664437 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121175459 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249324448 / 1.414213562 := by gcongr
      _ ≤ (0.000070343305 : ℝ) := by norm_num

end BstLean.Part269.N12828

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12828
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) ≤ 1.56614E-7 := by
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12828 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12828 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12828 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190435605 : ℝ) ^ 2 + 0.000121175459 ^ 2 + 3 * 0.000070343305 ^ 2 +
        2 * 0.797885 * 0.000190435605 * 0.000121175459 + 2 * 0.000190435605 * 0.000070343305 +
        4 * 0.797885 * 0.000121175459 * 0.000070343305 := by gcongr
    _ ≤ (1.56614E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12828 BstLean.Part154.csC Θ ≤ 0.002602138414 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12828 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12828 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12828 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035628550383 * 1.56614E-7 / (0.000249324062 : ℝ) := by gcongr
    _ ≤ 0.002602138414 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12828 BstLean.Part154.csC Θ ≤ 0.002886715385 + 0.000657520179 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12828 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12828 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035628550383 : ℝ) * ((2 * Θ * 0.000249324448 +
        (6863 / 10000) * 0.000249324448 * 12828 * 0.000997359955) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002886715385 + 0.000657520179 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12828 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12828 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12828 0.011 Θ ∧ gammaRatio 12828 0.011 Θ ≤ 0.000085711298 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12828 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035628550383 : ℝ) * 0.525 / ((1 - 0.011) * 12828) := by gcongr
      _ ≤ (0.000085711298 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12828 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12828 0.011 Θ) :=
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
    badAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12828 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12828 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12828 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12828 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12828 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12828 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12828 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12828 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12828 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12828 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035628550383 : ℝ) * 12828 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396377601 + 0.003259658593 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12828

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12828
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12828 BstLean.Part154.csC) (piBar (rhoBar 12828 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12828 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12828 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12828 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12828 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12828 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12828 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12828 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12828 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12828 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12828 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052218975326 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12828) ≤ 0.010544142294 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12828 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035628550383)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010544142294 + 2 * 0.737676 / 12828) := by gcongr
    _ ≤ (0.052218975326 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12828 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12828

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12828
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509299072 : ℝ) ≤ plow 12828 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12828) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614298363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366122668) : eMP 12828 0.011 xi bn ≤ 0.001176276272 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12828 : ℝ) * (1 - 0.011))) ≤ 0.000581623825 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366122668 / (12828 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581623825 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581623825 : ℝ) + 3.141593 * 0.052614298363 / (12828 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176276272 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614298363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366122668) : PiBarMP 12828 12 0.011 xi bn ≤ 0.160436322319 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12828 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036961096683 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.636104336043 : ℝ) ≤ √((12828 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.260761078142 : ℝ) ≤ √(12828 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12828) ≤ 0.123011783871 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036961096683 + 0.052614298363 * 1.772454 / (2 * (112.636104336043 : ℝ))) * (1 + 0.001176276272) +
        8 / (12828 * 113.260761078142) + 0.123011783871 := by gcongr
    _ ≤ (0.160436322319 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614298363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366122668) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281597043945) :
    parallelOracle 12828 0.011 xi bn cd ≤ 0.161416694211 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12828 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12828 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509299072 : ℝ) ≤ plow 12828 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.260761078142 : ℝ) ≤ √(12828 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281597043945 : ℝ) / (2 * 0.560509299072 * 113.260761078142)) * 0.160436322319 +
        0.281597043945 ^ 2 / (2 * 0.560509299072 * 113.260761078142) := by gcongr
    _ ≤ (0.161416694211 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614298363) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366122668)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281597043945) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12828 12828 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509299072 : ℝ) ≤ plow 12828 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.260761078142 : ℝ) ≤ √(12828 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12828 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12828 Θ 1.22 ≤ 0.011708384152 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.260761078142 := by gcongr <;> linarith
      _ ≤ (0.011708384152 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12828 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12828 12828 0.011 ≤ 0.008439701299 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12828 12828 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12828 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12828 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12828 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12828 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161416694211 + 0.011708384152 + (0.008439701299 : ℝ) *
        (1 + 2 * (0.281597043945 + 0.011708384152) / (0.560509299072 * 113.260761078142))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12828]

end BstLean.Part269.N12828

/-! The original eight local profiles supply actual 12828 moment certificates. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12828 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052614298363 ∧
    0 ≤ bN 12828 BstLean.Part154.csC (groupTheta g) ∧ bN 12828 BstLean.Part154.csC (groupTheta g) ≤ 0.001366122668 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12828 12828 0.011
      (momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12828 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12828 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12828 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229378068619 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12828 0.011
      (momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12828 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12828
/-! The actual computed-centre upper energy formula at 12828. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12828

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12828)
open BstLean.Part268 (cell12828)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085125481735
  | 2 => 0.086061718077
  | 3 => 0.086995174733
  | 4 => 0.087927055881
  | 5 => 0.088858824743
  | 6 => 0.089792242917
  | 7 => 0.090729413566
  | 8 => 0.091672828540
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12828 12828 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12828 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12828

/-! Actual upper energy certificates on all 43 source endpoints at 12828. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12828)
open BstLean.Part268 (cell12828)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12828 (gMinus 12828) (1 - (cell12828 i).lower) ≤ 1 ∧
    energyUpper 12828 (gMinus 12828) (BstLean.Part211.gPlus 12828)
      (finiteEnergy 12828 12828 0.011) (1 - (cell12828 i).lower) ≤
      (cell12828 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨10,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨11,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨12,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨13,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨14,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨15,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨16,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨17,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨18,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨19,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨20,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨21,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨22,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨23,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨24,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨25,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨26,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨27,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨28,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨29,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨30,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨31,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨32,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨33,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨34,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨35,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨36,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨37,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨38,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨39,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨40,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨41,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨42,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨43,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨44,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨45,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨46,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨47,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨48,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨49,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨50,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨51,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12828) (by norm_num)
        (q := 1 - (cell12828 ⟨52,by decide⟩).lower)
        (by norm_num [cell12828]) (by norm_num [cell12828])
      exact ⟨E.1,E.2.trans (by norm_num [cell12828])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12828

/-! Source-cell containment and simple scalar guards at 12828. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12828)
open BstLean.Part268 (cell12828)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12828 ⟨10,by decide⟩).lower ∧ (cell12828 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12828 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12828 ⟨11,by decide⟩).lower ∧ (cell12828 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12828 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12828 ⟨12,by decide⟩).lower ∧ (cell12828 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12828 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12828 ⟨13,by decide⟩).lower ∧ (cell12828 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12828 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12828 ⟨14,by decide⟩).lower ∧ (cell12828 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12828 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12828 ⟨15,by decide⟩).lower ∧ (cell12828 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12828 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12828 ⟨16,by decide⟩).lower ∧ (cell12828 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12828 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12828 ⟨17,by decide⟩).lower ∧ (cell12828 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12828 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12828 ⟨18,by decide⟩).lower ∧ (cell12828 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12828 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12828 ⟨19,by decide⟩).lower ∧ (cell12828 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12828 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12828 ⟨20,by decide⟩).lower ∧ (cell12828 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12828 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12828 ⟨21,by decide⟩).lower ∧ (cell12828 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12828 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12828 ⟨22,by decide⟩).lower ∧ (cell12828 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12828 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12828 ⟨23,by decide⟩).lower ∧ (cell12828 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12828 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12828 ⟨24,by decide⟩).lower ∧ (cell12828 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12828 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12828 ⟨25,by decide⟩).lower ∧ (cell12828 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12828 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12828 ⟨26,by decide⟩).lower ∧ (cell12828 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12828 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12828 ⟨27,by decide⟩).lower ∧ (cell12828 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12828 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12828 ⟨28,by decide⟩).lower ∧ (cell12828 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12828 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12828 ⟨29,by decide⟩).lower ∧ (cell12828 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12828 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12828 ⟨30,by decide⟩).lower ∧ (cell12828 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12828 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12828 ⟨31,by decide⟩).lower ∧ (cell12828 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12828 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12828 ⟨32,by decide⟩).lower ∧ (cell12828 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12828 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12828 ⟨33,by decide⟩).lower ∧ (cell12828 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12828 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12828 ⟨34,by decide⟩).lower ∧ (cell12828 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12828 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12828 ⟨35,by decide⟩).lower ∧ (cell12828 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12828 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12828 ⟨36,by decide⟩).lower ∧ (cell12828 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12828 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12828 ⟨37,by decide⟩).lower ∧ (cell12828 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12828 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12828 ⟨38,by decide⟩).lower ∧ (cell12828 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12828 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12828 ⟨39,by decide⟩).lower ∧ (cell12828 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12828 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12828 ⟨40,by decide⟩).lower ∧ (cell12828 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12828 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12828 ⟨41,by decide⟩).lower ∧ (cell12828 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12828 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12828 ⟨42,by decide⟩).lower ∧ (cell12828 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12828 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12828 ⟨43,by decide⟩).lower ∧ (cell12828 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12828 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12828 ⟨44,by decide⟩).lower ∧ (cell12828 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12828 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12828 ⟨45,by decide⟩).lower ∧ (cell12828 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12828 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12828 ⟨46,by decide⟩).lower ∧ (cell12828 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12828 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12828 ⟨47,by decide⟩).lower ∧ (cell12828 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12828 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12828 ⟨48,by decide⟩).lower ∧ (cell12828 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12828 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12828 ⟨49,by decide⟩).lower ∧ (cell12828 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12828 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12828 ⟨50,by decide⟩).lower ∧ (cell12828 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12828 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12828 ⟨51,by decide⟩).lower ∧ (cell12828 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12828 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12828 ⟨52,by decide⟩).lower ∧ (cell12828 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12828 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12828 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12828 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12828,cell12828,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12828 i).lower ∧
    (cell12828 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12828 i).upper ≤ (0.532 : ℝ) ∧
    (cell12828 i).centre ≤ (0.1 : ℝ) ∧ (cell12828 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12828 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12828 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12828

/-! The local source numeric instances at 12828 have no network premises. -/
namespace BstLean.Part269.N12828
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12828)
open BstLean.Part268 (cell12828)

noncomputable def sourceNumerics12828 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12828 (cell12828 i)
      scalarRow12828.M scalarRow12828.H scalarRow12828.xi := by
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
    energy_allowance := scalarRow12828.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12828]
    centre_nonneg := (scalarRow12828.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12828])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12828
/-! Actual 12829 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12829 ≤ (1.035627149610 : ℝ) := by
  have hr : (113.265175583671 : ℝ) ≤ √(12829 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.265175583671 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12829 12829 (11 / 1000) ≤
    (0.008439372360 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12829) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.265175583671 : ℝ) ≤ √(12829 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12829)
  have hdiv : K / √(12829 : ℝ) ≤ K / 113.265175583671 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.265175583671 ≤ (0.008439372360 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12829.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12829 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12829 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12829 := gPlus_lower 12829
end BstLean.Part269.N12829

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12829
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035627149609 : ℝ) ≤ wn 12829 := by
  have hn : √(12829 : ℝ) ≤ 113.265175583672 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12829 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.265175583672 ≤ 2 / √(12829 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249304291 : ℝ) ≤ rhoBar 12829 BstLean.Part154.csC ∧
    rhoBar 12829 BstLean.Part154.csC ≤ 0.000249304677 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035627149609 : ℝ) / (1.295212 * 12829) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035627149610 : ℝ) / (1.29521 * 12829) := by gcongr
      _ ≤ (0.000249304677 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12829 BstLean.Part154.csC) ≤ 0.000997280861 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12829 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) ≤ 0.000190420503 ∧
    cc1 (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) ≤ 0.000121165849 ∧
    cc2 (rhoBar 12829 BstLean.Part154.csC) ≤ 0.000070337727 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12829 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12829 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12829 BstLean.Part154.csC * nuR (rhoBar 12829 BstLean.Part154.csC)) ≤ 0.000498624893 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249304677 : ℝ) * 0.000997280861 := by gcongr
      _ ≤ (0.000498624893 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12829 BstLean.Part154.csC) * nuR (rhoBar 12829 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997280861 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12829 BstLean.Part154.csC) * rhoBar 12829 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249304677 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249304677 / 2 + 0.399 * 0.000997280861 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190420503 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498624893 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121165849 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249304677 / 1.414213562 := by gcongr
      _ ≤ (0.000070337727 : ℝ) := by norm_num

end BstLean.Part269.N12829

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12829
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) ≤ 1.56590E-7 := by
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12829 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12829 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12829 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190420503 : ℝ) ^ 2 + 0.000121165849 ^ 2 + 3 * 0.000070337727 ^ 2 +
        2 * 0.797885 * 0.000190420503 * 0.000121165849 + 2 * 0.000190420503 * 0.000070337727 +
        4 * 0.797885 * 0.000121165849 * 0.000070337727 := by gcongr
    _ ≤ (1.56590E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12829 BstLean.Part154.csC Θ ≤ 0.002601942465 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12829 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12829 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12829 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035627149610 * 1.56590E-7 / (0.000249304291 : ℝ) := by gcongr
    _ ≤ 0.002601942465 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12829 BstLean.Part154.csC Θ ≤ 0.002886478658 + 0.000657467150 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12829 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12829 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035627149610 : ℝ) * ((2 * Θ * 0.000249304677 +
        (6863 / 10000) * 0.000249304677 * 12829 * 0.000997280861) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002886478658 + 0.000657467150 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12829 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12829 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12829 0.011 Θ ∧ gammaRatio 12829 0.011 Θ ≤ 0.000085704501 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12829 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035627149610 : ℝ) * 0.525 / ((1 - 0.011) * 12829) := by gcongr
      _ ≤ (0.000085704501 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12829 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12829 0.011 Θ) :=
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
    badAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12829 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12829 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12829 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12829 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12829 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12829 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12829 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12829 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12829 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12829 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035627149610 : ℝ) * 12829 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396140874 + 0.003259409615 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12829

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12829
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12829 BstLean.Part154.csC) (piBar (rhoBar 12829 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12829 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12829 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12829 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12829 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12829 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12829 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12829 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12829 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12829 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12829 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052216918133 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12829) ≤ 0.010543731336 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12829 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035627149610)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010543731336 + 2 * 0.737676 / 12829) := by gcongr
    _ ≤ (0.052216918133 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12829 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12829

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12829
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509343393 : ℝ) ≤ plow 12829 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12829) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613930922)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366019795) : eMP 12829 0.011 xi bn ≤ 0.001176186031 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12829 : ℝ) * (1 - 0.011))) ≤ 0.000581579258 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366019795 / (12829 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581579258 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581579258 : ℝ) + 3.141593 * 0.052613930922 / (12829 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176186031 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613930922)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366019795) : PiBarMP 12829 12 0.011 xi bn ≤ 0.160430111574 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12829 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036959705018 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.640494494653 : ℝ) ≤ √((12829 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.265175583671 : ℝ) ≤ √(12829 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12829) ≤ 0.123006989492 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036959705018 + 0.052613930922 * 1.772454 / (2 * (112.640494494653 : ℝ))) * (1 + 0.001176186031) +
        8 / (12829 * 113.265175583671) + 0.123006989492 := by gcongr
    _ ≤ (0.160430111574 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613930922)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366019795) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281594185800) :
    parallelOracle 12829 0.011 xi bn cd ≤ 0.161410415115 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12829 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12829 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509343393 : ℝ) ≤ plow 12829 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.265175583671 : ℝ) ≤ √(12829 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281594185800 : ℝ) / (2 * 0.560509343393 * 113.265175583671)) * 0.160430111574 +
        0.281594185800 ^ 2 / (2 * 0.560509343393 * 113.265175583671) := by gcongr
    _ ≤ (0.161410415115 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613930922) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366019795)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281594185800) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12829 12829 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509343393 : ℝ) ≤ plow 12829 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.265175583671 : ℝ) ≤ √(12829 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12829 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12829 Θ 1.22 ≤ 0.011707927818 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.265175583671 := by gcongr <;> linarith
      _ ≤ (0.011707927818 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12829 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12829 12829 0.011 ≤ 0.008439372360 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12829 12829 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12829 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12829 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12829 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12829 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161410415115 + 0.011707927818 + (0.008439372360 : ℝ) *
        (1 + 2 * (0.281594185800 + 0.011707927818) / (0.560509343393 * 113.265175583671))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12829]

end BstLean.Part269.N12829

/-! The original eight local profiles supply actual 12829 moment certificates. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12829 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052613930922 ∧
    0 ≤ bN 12829 BstLean.Part154.csC (groupTheta g) ∧ bN 12829 BstLean.Part154.csC (groupTheta g) ≤ 0.001366019795 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12829 12829 0.011
      (momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12829 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12829 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12829 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229377267667 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12829 0.011
      (momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12829 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12829
/-! The actual computed-centre upper energy formula at 12829. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12829

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12829)
open BstLean.Part268 (cell12829)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085122696142
  | 2 => 0.086058884173
  | 3 => 0.086992285940
  | 4 => 0.087924104075
  | 5 => 0.088855799974
  | 6 => 0.089789133098
  | 7 => 0.090726204118
  | 8 => 0.091669502001
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12829 12829 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12829 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12829

/-! Actual upper energy certificates on all 43 source endpoints at 12829. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12829)
open BstLean.Part268 (cell12829)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12829 (gMinus 12829) (1 - (cell12829 i).lower) ≤ 1 ∧
    energyUpper 12829 (gMinus 12829) (BstLean.Part211.gPlus 12829)
      (finiteEnergy 12829 12829 0.011) (1 - (cell12829 i).lower) ≤
      (cell12829 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨10,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨11,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨12,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨13,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨14,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨15,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨16,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨17,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨18,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨19,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨20,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨21,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨22,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨23,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨24,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨25,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨26,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨27,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨28,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨29,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨30,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨31,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨32,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨33,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨34,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨35,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨36,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨37,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨38,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨39,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨40,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨41,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨42,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨43,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨44,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨45,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨46,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨47,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨48,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨49,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨50,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨51,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12829) (by norm_num)
        (q := 1 - (cell12829 ⟨52,by decide⟩).lower)
        (by norm_num [cell12829]) (by norm_num [cell12829])
      exact ⟨E.1,E.2.trans (by norm_num [cell12829])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12829

/-! Source-cell containment and simple scalar guards at 12829. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12829)
open BstLean.Part268 (cell12829)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12829 ⟨10,by decide⟩).lower ∧ (cell12829 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12829 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12829 ⟨11,by decide⟩).lower ∧ (cell12829 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12829 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12829 ⟨12,by decide⟩).lower ∧ (cell12829 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12829 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12829 ⟨13,by decide⟩).lower ∧ (cell12829 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12829 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12829 ⟨14,by decide⟩).lower ∧ (cell12829 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12829 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12829 ⟨15,by decide⟩).lower ∧ (cell12829 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12829 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12829 ⟨16,by decide⟩).lower ∧ (cell12829 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12829 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12829 ⟨17,by decide⟩).lower ∧ (cell12829 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12829 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12829 ⟨18,by decide⟩).lower ∧ (cell12829 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12829 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12829 ⟨19,by decide⟩).lower ∧ (cell12829 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12829 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12829 ⟨20,by decide⟩).lower ∧ (cell12829 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12829 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12829 ⟨21,by decide⟩).lower ∧ (cell12829 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12829 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12829 ⟨22,by decide⟩).lower ∧ (cell12829 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12829 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12829 ⟨23,by decide⟩).lower ∧ (cell12829 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12829 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12829 ⟨24,by decide⟩).lower ∧ (cell12829 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12829 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12829 ⟨25,by decide⟩).lower ∧ (cell12829 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12829 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12829 ⟨26,by decide⟩).lower ∧ (cell12829 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12829 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12829 ⟨27,by decide⟩).lower ∧ (cell12829 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12829 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12829 ⟨28,by decide⟩).lower ∧ (cell12829 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12829 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12829 ⟨29,by decide⟩).lower ∧ (cell12829 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12829 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12829 ⟨30,by decide⟩).lower ∧ (cell12829 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12829 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12829 ⟨31,by decide⟩).lower ∧ (cell12829 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12829 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12829 ⟨32,by decide⟩).lower ∧ (cell12829 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12829 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12829 ⟨33,by decide⟩).lower ∧ (cell12829 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12829 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12829 ⟨34,by decide⟩).lower ∧ (cell12829 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12829 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12829 ⟨35,by decide⟩).lower ∧ (cell12829 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12829 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12829 ⟨36,by decide⟩).lower ∧ (cell12829 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12829 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12829 ⟨37,by decide⟩).lower ∧ (cell12829 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12829 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12829 ⟨38,by decide⟩).lower ∧ (cell12829 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12829 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12829 ⟨39,by decide⟩).lower ∧ (cell12829 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12829 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12829 ⟨40,by decide⟩).lower ∧ (cell12829 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12829 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12829 ⟨41,by decide⟩).lower ∧ (cell12829 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12829 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12829 ⟨42,by decide⟩).lower ∧ (cell12829 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12829 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12829 ⟨43,by decide⟩).lower ∧ (cell12829 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12829 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12829 ⟨44,by decide⟩).lower ∧ (cell12829 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12829 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12829 ⟨45,by decide⟩).lower ∧ (cell12829 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12829 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12829 ⟨46,by decide⟩).lower ∧ (cell12829 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12829 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12829 ⟨47,by decide⟩).lower ∧ (cell12829 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12829 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12829 ⟨48,by decide⟩).lower ∧ (cell12829 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12829 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12829 ⟨49,by decide⟩).lower ∧ (cell12829 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12829 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12829 ⟨50,by decide⟩).lower ∧ (cell12829 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12829 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12829 ⟨51,by decide⟩).lower ∧ (cell12829 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12829 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12829 ⟨52,by decide⟩).lower ∧ (cell12829 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12829 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12829 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12829 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12829,cell12829,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12829 i).lower ∧
    (cell12829 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12829 i).upper ≤ (0.532 : ℝ) ∧
    (cell12829 i).centre ≤ (0.1 : ℝ) ∧ (cell12829 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12829 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12829 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12829

/-! The local source numeric instances at 12829 have no network premises. -/
namespace BstLean.Part269.N12829
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12829)
open BstLean.Part268 (cell12829)

noncomputable def sourceNumerics12829 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12829 (cell12829 i)
      scalarRow12829.M scalarRow12829.H scalarRow12829.xi := by
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
    energy_allowance := scalarRow12829.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12829]
    centre_nonneg := (scalarRow12829.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12829])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12829
/-! Actual 12830 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12830 ≤ (1.035625749000 : ℝ) := by
  have hr : (113.269589917152 : ℝ) ≤ √(12830 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.269589917152 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12830 12830 (11 / 1000) ≤
    (0.008439043459 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12830) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.269589917152 : ℝ) ≤ √(12830 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12830)
  have hdiv : K / √(12830 : ℝ) ≤ K / 113.269589917152 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.269589917152 ≤ (0.008439043459 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12830.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12830 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12830 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12830 := gPlus_lower 12830
end BstLean.Part269.N12830

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12830
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035625748999 : ℝ) ≤ wn 12830 := by
  have hn : √(12830 : ℝ) ≤ 113.269589917153 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12830 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.269589917153 ≤ 2 / √(12830 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249284522 : ℝ) ≤ rhoBar 12830 BstLean.Part154.csC ∧
    rhoBar 12830 BstLean.Part154.csC ≤ 0.000249284908 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035625748999 : ℝ) / (1.295212 * 12830) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035625749000 : ℝ) / (1.29521 * 12830) := by gcongr
      _ ≤ (0.000249284908 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12830 BstLean.Part154.csC) ≤ 0.000997201775 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12830 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) ≤ 0.000190405403 ∧
    cc1 (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) ≤ 0.000121156241 ∧
    cc2 (rhoBar 12830 BstLean.Part154.csC) ≤ 0.000070332149 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12830 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12830 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12830 BstLean.Part154.csC * nuR (rhoBar 12830 BstLean.Part154.csC)) ≤ 0.000498585352 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249284908 : ℝ) * 0.000997201775 := by gcongr
      _ ≤ (0.000498585352 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12830 BstLean.Part154.csC) * nuR (rhoBar 12830 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997201775 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12830 BstLean.Part154.csC) * rhoBar 12830 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249284908 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249284908 / 2 + 0.399 * 0.000997201775 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190405403 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498585352 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121156241 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249284908 / 1.414213562 := by gcongr
      _ ≤ (0.000070332149 : ℝ) := by norm_num

end BstLean.Part269.N12830

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12830
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) ≤ 1.56565E-7 := by
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12830 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12830 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12830 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190405403 : ℝ) ^ 2 + 0.000121156241 ^ 2 + 3 * 0.000070332149 ^ 2 +
        2 * 0.797885 * 0.000190405403 * 0.000121156241 + 2 * 0.000190405403 * 0.000070332149 +
        4 * 0.797885 * 0.000121156241 * 0.000070332149 := by gcongr
    _ ≤ (1.56565E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12830 BstLean.Part154.csC Θ ≤ 0.002601729849 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12830 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12830 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12830 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035625749000 * 1.56565E-7 / (0.000249284522 : ℝ) := by gcongr
    _ ≤ 0.002601729849 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12830 BstLean.Part154.csC Θ ≤ 0.002886241943 + 0.000657414126 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12830 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12830 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035625749000 : ℝ) * ((2 * Θ * 0.000249284908 +
        (6863 / 10000) * 0.000249284908 * 12830 * 0.000997201775) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002886241943 + 0.000657414126 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12830 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12830 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12830 0.011 Θ ∧ gammaRatio 12830 0.011 Θ ≤ 0.000085697705 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12830 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035625749000 : ℝ) * 0.525 / ((1 - 0.011) * 12830) := by gcongr
      _ ≤ (0.000085697705 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12830 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12830 0.011 Θ) :=
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
    badAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12830 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12830 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12830 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12830 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12830 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12830 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12830 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12830 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12830 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12830 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035625749000 : ℝ) * 12830 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003395904159 + 0.003259143975 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12830

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12830
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12830 BstLean.Part154.csC) (piBar (rhoBar 12830 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12830 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12830 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12830 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12830 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12830 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12830 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12830 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12830 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12830 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12830 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052214861186 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12830) ≤ 0.010543320427 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12830 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035625749000)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010543320427 + 2 * 0.737676 / 12830) := by gcongr
    _ ≤ (0.052214861186 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12830 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12830

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12830
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509387708 : ℝ) ≤ plow 12830 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12830) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613554746)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365908171) : eMP 12830 0.011 xi bn ≤ 0.001176092069 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12830 : ℝ) * (1 - 0.011))) ≤ 0.000581532831 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365908171 / (12830 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581532831 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581532831 : ℝ) + 3.141593 * 0.052613554746 / (12830 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176092069 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613554746)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365908171) : PiBarMP 12830 12 0.011 xi bn ≤ 0.160423782601 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12830 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036958194910 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.644884482163 : ℝ) ≤ √((12830 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.269589917152 : ℝ) ≤ √(12830 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12830) ≤ 0.123002195673 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036958194910 + 0.052613554746 * 1.772454 / (2 * (112.644884482163 : ℝ))) * (1 + 0.001176092069) +
        8 / (12830 * 113.269589917152) + 0.123002195673 := by gcongr
    _ ≤ (0.160423782601 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613554746)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365908171) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281591308857) :
    parallelOracle 12830 0.011 xi bn cd ≤ 0.161404017430 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12830 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12830 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509387708 : ℝ) ≤ plow 12830 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.269589917152 : ℝ) ≤ √(12830 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281591308857 : ℝ) / (2 * 0.560509387708 * 113.269589917152)) * 0.160423782601 +
        0.281591308857 ^ 2 / (2 * 0.560509387708 * 113.269589917152) := by gcongr
    _ ≤ (0.161404017430 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613554746) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365908171)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281591308857) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12830 12830 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509387708 : ℝ) ≤ plow 12830 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.269589917152 : ℝ) ≤ √(12830 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12830 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12830 Θ 1.22 ≤ 0.011707471538 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.269589917152 := by gcongr <;> linarith
      _ ≤ (0.011707471538 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12830 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12830 12830 0.011 ≤ 0.008439043459 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12830 12830 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12830 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12830 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12830 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12830 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161404017430 + 0.011707471538 + (0.008439043459 : ℝ) *
        (1 + 2 * (0.281591308857 + 0.011707471538) / (0.560509387708 * 113.269589917152))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12830]

end BstLean.Part269.N12830

/-! The original eight local profiles supply actual 12830 moment certificates. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12830 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052613554746 ∧
    0 ≤ bN 12830 BstLean.Part154.csC (groupTheta g) ∧ bN 12830 BstLean.Part154.csC (groupTheta g) ≤ 0.001365908171 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12830 12830 0.011
      (momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12830 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12830 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12830 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229376447671 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12830 0.011
      (momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12830 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12830
/-! The actual computed-centre upper energy formula at 12830. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12830

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12830)
open BstLean.Part268 (cell12830)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085119911503
  | 2 => 0.086056051260
  | 3 => 0.086989398184
  | 4 => 0.087921153363
  | 5 => 0.088852776371
  | 6 => 0.089786024530
  | 7 => 0.090722996023
  | 8 => 0.091666176939
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12830 12830 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12830 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12830

/-! Actual upper energy certificates on all 43 source endpoints at 12830. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12830)
open BstLean.Part268 (cell12830)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12830 (gMinus 12830) (1 - (cell12830 i).lower) ≤ 1 ∧
    energyUpper 12830 (gMinus 12830) (BstLean.Part211.gPlus 12830)
      (finiteEnergy 12830 12830 0.011) (1 - (cell12830 i).lower) ≤
      (cell12830 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨10,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨11,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨12,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨13,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨14,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨15,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨16,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨17,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨18,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨19,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨20,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨21,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨22,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨23,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨24,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨25,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨26,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨27,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨28,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨29,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨30,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨31,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨32,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨33,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨34,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨35,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨36,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨37,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨38,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨39,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨40,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨41,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨42,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨43,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨44,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨45,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨46,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨47,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨48,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨49,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨50,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨51,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12830) (by norm_num)
        (q := 1 - (cell12830 ⟨52,by decide⟩).lower)
        (by norm_num [cell12830]) (by norm_num [cell12830])
      exact ⟨E.1,E.2.trans (by norm_num [cell12830])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12830

/-! Source-cell containment and simple scalar guards at 12830. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12830)
open BstLean.Part268 (cell12830)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12830 ⟨10,by decide⟩).lower ∧ (cell12830 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12830 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12830 ⟨11,by decide⟩).lower ∧ (cell12830 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12830 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12830 ⟨12,by decide⟩).lower ∧ (cell12830 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12830 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12830 ⟨13,by decide⟩).lower ∧ (cell12830 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12830 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12830 ⟨14,by decide⟩).lower ∧ (cell12830 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12830 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12830 ⟨15,by decide⟩).lower ∧ (cell12830 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12830 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12830 ⟨16,by decide⟩).lower ∧ (cell12830 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12830 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12830 ⟨17,by decide⟩).lower ∧ (cell12830 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12830 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12830 ⟨18,by decide⟩).lower ∧ (cell12830 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12830 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12830 ⟨19,by decide⟩).lower ∧ (cell12830 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12830 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12830 ⟨20,by decide⟩).lower ∧ (cell12830 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12830 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12830 ⟨21,by decide⟩).lower ∧ (cell12830 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12830 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12830 ⟨22,by decide⟩).lower ∧ (cell12830 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12830 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12830 ⟨23,by decide⟩).lower ∧ (cell12830 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12830 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12830 ⟨24,by decide⟩).lower ∧ (cell12830 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12830 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12830 ⟨25,by decide⟩).lower ∧ (cell12830 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12830 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12830 ⟨26,by decide⟩).lower ∧ (cell12830 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12830 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12830 ⟨27,by decide⟩).lower ∧ (cell12830 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12830 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12830 ⟨28,by decide⟩).lower ∧ (cell12830 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12830 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12830 ⟨29,by decide⟩).lower ∧ (cell12830 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12830 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12830 ⟨30,by decide⟩).lower ∧ (cell12830 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12830 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12830 ⟨31,by decide⟩).lower ∧ (cell12830 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12830 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12830 ⟨32,by decide⟩).lower ∧ (cell12830 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12830 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12830 ⟨33,by decide⟩).lower ∧ (cell12830 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12830 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12830 ⟨34,by decide⟩).lower ∧ (cell12830 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12830 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12830 ⟨35,by decide⟩).lower ∧ (cell12830 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12830 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12830 ⟨36,by decide⟩).lower ∧ (cell12830 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12830 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12830 ⟨37,by decide⟩).lower ∧ (cell12830 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12830 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12830 ⟨38,by decide⟩).lower ∧ (cell12830 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12830 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12830 ⟨39,by decide⟩).lower ∧ (cell12830 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12830 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12830 ⟨40,by decide⟩).lower ∧ (cell12830 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12830 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12830 ⟨41,by decide⟩).lower ∧ (cell12830 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12830 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12830 ⟨42,by decide⟩).lower ∧ (cell12830 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12830 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12830 ⟨43,by decide⟩).lower ∧ (cell12830 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12830 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12830 ⟨44,by decide⟩).lower ∧ (cell12830 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12830 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12830 ⟨45,by decide⟩).lower ∧ (cell12830 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12830 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12830 ⟨46,by decide⟩).lower ∧ (cell12830 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12830 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12830 ⟨47,by decide⟩).lower ∧ (cell12830 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12830 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12830 ⟨48,by decide⟩).lower ∧ (cell12830 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12830 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12830 ⟨49,by decide⟩).lower ∧ (cell12830 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12830 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12830 ⟨50,by decide⟩).lower ∧ (cell12830 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12830 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12830 ⟨51,by decide⟩).lower ∧ (cell12830 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12830 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12830 ⟨52,by decide⟩).lower ∧ (cell12830 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12830 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12830 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12830 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12830,cell12830,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12830 i).lower ∧
    (cell12830 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12830 i).upper ≤ (0.532 : ℝ) ∧
    (cell12830 i).centre ≤ (0.1 : ℝ) ∧ (cell12830 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12830 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12830 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12830

/-! The local source numeric instances at 12830 have no network premises. -/
namespace BstLean.Part269.N12830
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12830)
open BstLean.Part268 (cell12830)

noncomputable def sourceNumerics12830 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12830 (cell12830 i)
      scalarRow12830.M scalarRow12830.H scalarRow12830.xi := by
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
    energy_allowance := scalarRow12830.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12830]
    centre_nonneg := (scalarRow12830.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12830])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12830
/-! Actual 12831 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12831 ≤ (1.035624348556 : ℝ) := by
  have hr : (113.274004078605 : ℝ) ≤ √(12831 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.274004078605 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12831 12831 (11 / 1000) ≤
    (0.008438714596 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12831) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.274004078605 : ℝ) ≤ √(12831 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12831)
  have hdiv : K / √(12831 : ℝ) ≤ K / 113.274004078605 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.274004078605 ≤ (0.008438714596 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12831.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12831 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12831 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12831 := gPlus_lower 12831
end BstLean.Part269.N12831

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12831
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035624348555 : ℝ) ≤ wn 12831 := by
  have hn : √(12831 : ℝ) ≤ 113.274004078606 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12831 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.274004078606 ≤ 2 / √(12831 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249264757 : ℝ) ≤ rhoBar 12831 BstLean.Part154.csC ∧
    rhoBar 12831 BstLean.Part154.csC ≤ 0.000249265143 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035624348555 : ℝ) / (1.295212 * 12831) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035624348556 : ℝ) / (1.29521 * 12831) := by gcongr
      _ ≤ (0.000249265143 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12831 BstLean.Part154.csC) ≤ 0.000997122706 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12831 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) ≤ 0.000190390306 ∧
    cc1 (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) ≤ 0.000121146635 ∧
    cc2 (rhoBar 12831 BstLean.Part154.csC) ≤ 0.000070326573 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12831 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12831 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12831 BstLean.Part154.csC * nuR (rhoBar 12831 BstLean.Part154.csC)) ≤ 0.000498545820 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249265143 : ℝ) * 0.000997122706 := by gcongr
      _ ≤ (0.000498545820 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12831 BstLean.Part154.csC) * nuR (rhoBar 12831 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997122706 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12831 BstLean.Part154.csC) * rhoBar 12831 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249265143 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249265143 / 2 + 0.399 * 0.000997122706 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190390306 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498545820 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121146635 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249265143 / 1.414213562 := by gcongr
      _ ≤ (0.000070326573 : ℝ) := by norm_num

end BstLean.Part269.N12831

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12831
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) ≤ 1.56540E-7 := by
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12831 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12831 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12831 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190390306 : ℝ) ^ 2 + 0.000121146635 ^ 2 + 3 * 0.000070326573 ^ 2 +
        2 * 0.797885 * 0.000190390306 * 0.000121146635 + 2 * 0.000190390306 * 0.000070326573 +
        4 * 0.797885 * 0.000121146635 * 0.000070326573 := by gcongr
    _ ≤ (1.56540E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12831 BstLean.Part154.csC Θ ≤ 0.002601517158 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12831 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12831 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12831 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035624348556 * 1.56540E-7 / (0.000249264757 : ℝ) := by gcongr
    _ ≤ 0.002601517158 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12831 BstLean.Part154.csC Θ ≤ 0.002886005290 + 0.000657361113 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12831 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12831 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035624348556 : ℝ) * ((2 * Θ * 0.000249265143 +
        (6863 / 10000) * 0.000249265143 * 12831 * 0.000997122706) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002886005290 + 0.000657361113 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12831 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12831 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12831 0.011 Θ ∧ gammaRatio 12831 0.011 Θ ≤ 0.000085690911 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12831 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035624348556 : ℝ) * 0.525 / ((1 - 0.011) * 12831) := by gcongr
      _ ≤ (0.000085690911 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12831 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12831 0.011 Θ) :=
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
    badAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12831 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12831 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12831 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12831 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12831 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12831 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12831 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12831 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12831 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12831 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035624348556 : ℝ) * 12831 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003395667506 + 0.003258878271 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12831

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12831
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12831 BstLean.Part154.csC) (piBar (rhoBar 12831 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12831 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12831 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12831 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12831 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12831 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12831 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12831 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12831 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12831 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12831 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052212804476 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12831) ≤ 0.010542909565 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12831 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035624348556)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010542909565 + 2 * 0.737676 / 12831) := by gcongr
    _ ≤ (0.052212804476 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12831 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12831

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12831
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509432016 : ℝ) ≤ plow 12831 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12831) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613178599)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365796508) : eMP 12831 0.011 xi bn ≤ 0.001175998096 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12831 : ℝ) * (1 - 0.011))) ≤ 0.000581486399 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365796508 / (12831 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581486399 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581486399 : ℝ) + 3.141593 * 0.052613178599 / (12831 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175998096 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613178599)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365796508) : PiBarMP 12831 12 0.011 xi bn ≤ 0.160417453602 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12831 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036956684213 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.649274298594 : ℝ) ≤ √((12831 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.274004078605 : ℝ) ≤ √(12831 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12831) ≤ 0.122997402415 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036956684213 + 0.052613178599 * 1.772454 / (2 * (112.649274298594 : ℝ))) * (1 + 0.001175998096) +
        8 / (12831 * 113.274004078605) + 0.122997402415 := by gcongr
    _ ≤ (0.160417453602 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613178599)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365796508) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281588432212) :
    parallelOracle 12831 0.011 xi bn cd ≤ 0.161397619728 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12831 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12831 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509432016 : ℝ) ≤ plow 12831 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.274004078605 : ℝ) ≤ √(12831 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281588432212 : ℝ) / (2 * 0.560509432016 * 113.274004078605)) * 0.160417453602 +
        0.281588432212 ^ 2 / (2 * 0.560509432016 * 113.274004078605) := by gcongr
    _ ≤ (0.161397619728 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052613178599) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365796508)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281588432212) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12831 12831 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509432016 : ℝ) ≤ plow 12831 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.274004078605 : ℝ) ≤ √(12831 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12831 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12831 Θ 1.22 ≤ 0.011707015311 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.274004078605 := by gcongr <;> linarith
      _ ≤ (0.011707015311 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12831 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12831 12831 0.011 ≤ 0.008438714596 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12831 12831 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12831 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12831 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12831 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12831 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161397619728 + 0.011707015311 + (0.008438714596 : ℝ) *
        (1 + 2 * (0.281588432212 + 0.011707015311) / (0.560509432016 * 113.274004078605))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12831]

end BstLean.Part269.N12831

/-! The original eight local profiles supply actual 12831 moment certificates. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12831 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052613178599 ∧
    0 ≤ bN 12831 BstLean.Part154.csC (groupTheta g) ∧ bN 12831 BstLean.Part154.csC (groupTheta g) ≤ 0.001365796508 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12831 12831 0.011
      (momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12831 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12831 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12831 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229375627736 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12831 0.011
      (momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12831 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12831
/-! The actual computed-centre upper energy formula at 12831. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12831

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12831)
open BstLean.Part268 (cell12831)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085117127817
  | 2 => 0.086053219337
  | 3 => 0.086986511466
  | 4 => 0.087918203746
  | 5 => 0.088849753931
  | 6 => 0.089782917210
  | 7 => 0.090719789281
  | 8 => 0.091662853354
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12831 12831 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12831 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12831

/-! Actual upper energy certificates on all 43 source endpoints at 12831. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12831)
open BstLean.Part268 (cell12831)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12831 (gMinus 12831) (1 - (cell12831 i).lower) ≤ 1 ∧
    energyUpper 12831 (gMinus 12831) (BstLean.Part211.gPlus 12831)
      (finiteEnergy 12831 12831 0.011) (1 - (cell12831 i).lower) ≤
      (cell12831 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨10,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨11,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨12,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨13,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨14,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨15,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨16,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨17,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨18,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨19,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨20,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨21,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨22,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨23,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨24,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨25,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨26,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨27,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨28,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨29,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨30,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨31,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨32,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨33,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨34,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨35,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨36,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨37,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨38,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨39,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨40,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨41,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨42,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨43,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨44,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨45,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨46,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨47,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨48,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨49,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨50,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨51,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12831) (by norm_num)
        (q := 1 - (cell12831 ⟨52,by decide⟩).lower)
        (by norm_num [cell12831]) (by norm_num [cell12831])
      exact ⟨E.1,E.2.trans (by norm_num [cell12831])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12831

/-! Source-cell containment and simple scalar guards at 12831. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12831)
open BstLean.Part268 (cell12831)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12831 ⟨10,by decide⟩).lower ∧ (cell12831 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12831 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12831 ⟨11,by decide⟩).lower ∧ (cell12831 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12831 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12831 ⟨12,by decide⟩).lower ∧ (cell12831 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12831 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12831 ⟨13,by decide⟩).lower ∧ (cell12831 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12831 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12831 ⟨14,by decide⟩).lower ∧ (cell12831 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12831 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12831 ⟨15,by decide⟩).lower ∧ (cell12831 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12831 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12831 ⟨16,by decide⟩).lower ∧ (cell12831 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12831 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12831 ⟨17,by decide⟩).lower ∧ (cell12831 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12831 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12831 ⟨18,by decide⟩).lower ∧ (cell12831 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12831 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12831 ⟨19,by decide⟩).lower ∧ (cell12831 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12831 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12831 ⟨20,by decide⟩).lower ∧ (cell12831 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12831 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12831 ⟨21,by decide⟩).lower ∧ (cell12831 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12831 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12831 ⟨22,by decide⟩).lower ∧ (cell12831 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12831 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12831 ⟨23,by decide⟩).lower ∧ (cell12831 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12831 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12831 ⟨24,by decide⟩).lower ∧ (cell12831 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12831 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12831 ⟨25,by decide⟩).lower ∧ (cell12831 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12831 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12831 ⟨26,by decide⟩).lower ∧ (cell12831 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12831 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12831 ⟨27,by decide⟩).lower ∧ (cell12831 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12831 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12831 ⟨28,by decide⟩).lower ∧ (cell12831 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12831 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12831 ⟨29,by decide⟩).lower ∧ (cell12831 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12831 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12831 ⟨30,by decide⟩).lower ∧ (cell12831 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12831 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12831 ⟨31,by decide⟩).lower ∧ (cell12831 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12831 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12831 ⟨32,by decide⟩).lower ∧ (cell12831 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12831 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12831 ⟨33,by decide⟩).lower ∧ (cell12831 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12831 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12831 ⟨34,by decide⟩).lower ∧ (cell12831 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12831 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12831 ⟨35,by decide⟩).lower ∧ (cell12831 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12831 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12831 ⟨36,by decide⟩).lower ∧ (cell12831 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12831 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12831 ⟨37,by decide⟩).lower ∧ (cell12831 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12831 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12831 ⟨38,by decide⟩).lower ∧ (cell12831 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12831 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12831 ⟨39,by decide⟩).lower ∧ (cell12831 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12831 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12831 ⟨40,by decide⟩).lower ∧ (cell12831 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12831 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12831 ⟨41,by decide⟩).lower ∧ (cell12831 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12831 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12831 ⟨42,by decide⟩).lower ∧ (cell12831 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12831 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12831 ⟨43,by decide⟩).lower ∧ (cell12831 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12831 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12831 ⟨44,by decide⟩).lower ∧ (cell12831 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12831 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12831 ⟨45,by decide⟩).lower ∧ (cell12831 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12831 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12831 ⟨46,by decide⟩).lower ∧ (cell12831 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12831 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12831 ⟨47,by decide⟩).lower ∧ (cell12831 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12831 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12831 ⟨48,by decide⟩).lower ∧ (cell12831 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12831 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12831 ⟨49,by decide⟩).lower ∧ (cell12831 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12831 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12831 ⟨50,by decide⟩).lower ∧ (cell12831 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12831 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12831 ⟨51,by decide⟩).lower ∧ (cell12831 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12831 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12831 ⟨52,by decide⟩).lower ∧ (cell12831 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12831 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12831 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12831 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12831,cell12831,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12831 i).lower ∧
    (cell12831 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12831 i).upper ≤ (0.532 : ℝ) ∧
    (cell12831 i).centre ≤ (0.1 : ℝ) ∧ (cell12831 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12831 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12831 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12831

/-! The local source numeric instances at 12831 have no network premises. -/
namespace BstLean.Part269.N12831
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12831)
open BstLean.Part268 (cell12831)

noncomputable def sourceNumerics12831 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12831 (cell12831 i)
      scalarRow12831.M scalarRow12831.H scalarRow12831.xi := by
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
    energy_allowance := scalarRow12831.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12831]
    centre_nonneg := (scalarRow12831.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12831])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12831
/-! Actual 12832 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12832 ≤ (1.035622948276 : ℝ) := by
  have hr : (113.278418068050 : ℝ) ≤ √(12832 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.278418068050 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12832 12832 (11 / 1000) ≤
    (0.008438385772 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12832) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.278418068050 : ℝ) ≤ √(12832 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12832)
  have hdiv : K / √(12832 : ℝ) ≤ K / 113.278418068050 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.278418068050 ≤ (0.008438385772 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12832.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12832 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12832 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12832 := gPlus_lower 12832
end BstLean.Part269.N12832

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12832
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035622948275 : ℝ) ≤ wn 12832 := by
  have hn : √(12832 : ℝ) ≤ 113.278418068051 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12832 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.278418068051 ≤ 2 / √(12832 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249244995 : ℝ) ≤ rhoBar 12832 BstLean.Part154.csC ∧
    rhoBar 12832 BstLean.Part154.csC ≤ 0.000249245380 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035622948275 : ℝ) / (1.295212 * 12832) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035622948276 : ℝ) / (1.29521 * 12832) := by gcongr
      _ ≤ (0.000249245380 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12832 BstLean.Part154.csC) ≤ 0.000997043644 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12832 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) ≤ 0.000190375210 ∧
    cc1 (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) ≤ 0.000121137029 ∧
    cc2 (rhoBar 12832 BstLean.Part154.csC) ≤ 0.000070320997 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12832 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12832 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12832 BstLean.Part154.csC * nuR (rhoBar 12832 BstLean.Part154.csC)) ≤ 0.000498506291 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249245380 : ℝ) * 0.000997043644 := by gcongr
      _ ≤ (0.000498506291 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12832 BstLean.Part154.csC) * nuR (rhoBar 12832 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997043644 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12832 BstLean.Part154.csC) * rhoBar 12832 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249245380 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249245380 / 2 + 0.399 * 0.000997043644 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190375210 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498506291 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121137029 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249245380 / 1.414213562 := by gcongr
      _ ≤ (0.000070320997 : ℝ) := by norm_num

end BstLean.Part269.N12832

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12832
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) ≤ 1.56515E-7 := by
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12832 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12832 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12832 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190375210 : ℝ) ^ 2 + 0.000121137029 ^ 2 + 3 * 0.000070320997 ^ 2 +
        2 * 0.797885 * 0.000190375210 * 0.000121137029 + 2 * 0.000190375210 * 0.000070320997 +
        4 * 0.797885 * 0.000121137029 * 0.000070320997 := by gcongr
    _ ≤ (1.56515E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12832 BstLean.Part154.csC Θ ≤ 0.002601304404 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12832 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12832 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12832 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035622948276 * 1.56515E-7 / (0.000249244995 : ℝ) := by gcongr
    _ ≤ 0.002601304404 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12832 BstLean.Part154.csC Θ ≤ 0.002885768646 + 0.000657308105 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12832 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12832 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035622948276 : ℝ) * ((2 * Θ * 0.000249245380 +
        (6863 / 10000) * 0.000249245380 * 12832 * 0.000997043644) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002885768646 + 0.000657308105 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12832 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12832 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12832 0.011 Θ ∧ gammaRatio 12832 0.011 Θ ≤ 0.000085684117 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12832 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035622948276 : ℝ) * 0.525 / ((1 - 0.011) * 12832) := by gcongr
      _ ≤ (0.000085684117 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12832 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12832 0.011 Θ) :=
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
    badAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12832 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12832 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12832 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12832 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12832 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12832 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12832 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12832 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12832 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12832 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035622948276 : ℝ) * 12832 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003395430862 + 0.003258612509 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12832

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12832
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12832 BstLean.Part154.csC) (piBar (rhoBar 12832 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12832 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12832 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12832 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12832 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12832 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12832 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12832 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12832 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12832 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12832 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052210748013 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12832) ≤ 0.010542498752 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12832 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035622948276)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010542498752 + 2 * 0.737676 / 12832) := by gcongr
    _ ≤ (0.052210748013 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12832 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12832

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12832
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509476317 : ℝ) ≤ plow 12832 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12832) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612802430)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365684813) : eMP 12832 0.011 xi bn ≤ 0.001175904120 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12832 : ℝ) * (1 - 0.011))) ≤ 0.000581439965 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365684813 / (12832 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581439965 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581439965 : ℝ) + 3.141593 * 0.052612802430 / (12832 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175904120 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612802430)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365684813) : PiBarMP 12832 12 0.011 xi bn ≤ 0.160411124669 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12832 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036955173021 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.653663943965 : ℝ) ≤ √((12832 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.278418068050 : ℝ) ≤ √(12832 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12832) ≤ 0.122992609717 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036955173021 + 0.052612802430 * 1.772454 / (2 * (112.653663943965 : ℝ))) * (1 + 0.001175904120) +
        8 / (12832 * 113.278418068050) + 0.122992609717 := by gcongr
    _ ≤ (0.160411124669 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612802430)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365684813) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281585555763) :
    parallelOracle 12832 0.011 xi bn cd ≤ 0.161391222100 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12832 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12832 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509476317 : ℝ) ≤ plow 12832 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.278418068050 : ℝ) ≤ √(12832 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281585555763 : ℝ) / (2 * 0.560509476317 * 113.278418068050)) * 0.160411124669 +
        0.281585555763 ^ 2 / (2 * 0.560509476317 * 113.278418068050) := by gcongr
    _ ≤ (0.161391222100 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612802430) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365684813)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281585555763) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12832 12832 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509476317 : ℝ) ≤ plow 12832 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.278418068050 : ℝ) ≤ √(12832 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12832 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12832 Θ 1.22 ≤ 0.011706559137 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.278418068050 := by gcongr <;> linarith
      _ ≤ (0.011706559137 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12832 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12832 12832 0.011 ≤ 0.008438385772 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12832 12832 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12832 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12832 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12832 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12832 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161391222100 + 0.011706559137 + (0.008438385772 : ℝ) *
        (1 + 2 * (0.281585555763 + 0.011706559137) / (0.560509476317 * 113.278418068050))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12832]

end BstLean.Part269.N12832

/-! The original eight local profiles supply actual 12832 moment certificates. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12832 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052612802430 ∧
    0 ≤ bN 12832 BstLean.Part154.csC (groupTheta g) ∧ bN 12832 BstLean.Part154.csC (groupTheta g) ≤ 0.001365684813 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12832 12832 0.011
      (momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12832 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12832 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12832 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229374807750 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12832 0.011
      (momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12832 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12832
/-! The actual computed-centre upper energy formula at 12832. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12832

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12832)
open BstLean.Part268 (cell12832)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085114345082
  | 2 => 0.086050388404
  | 3 => 0.086983625782
  | 4 => 0.087915255220
  | 5 => 0.088846732654
  | 6 => 0.089779811137
  | 7 => 0.090716583889
  | 8 => 0.091659531244
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12832 12832 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12832 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12832

/-! Actual upper energy certificates on all 43 source endpoints at 12832. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12832)
open BstLean.Part268 (cell12832)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12832 (gMinus 12832) (1 - (cell12832 i).lower) ≤ 1 ∧
    energyUpper 12832 (gMinus 12832) (BstLean.Part211.gPlus 12832)
      (finiteEnergy 12832 12832 0.011) (1 - (cell12832 i).lower) ≤
      (cell12832 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨10,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨11,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨12,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨13,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨14,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨15,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨16,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨17,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨18,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨19,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨20,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨21,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨22,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨23,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨24,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨25,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨26,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨27,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨28,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨29,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨30,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨31,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨32,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨33,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨34,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨35,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨36,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨37,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨38,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨39,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨40,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨41,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨42,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨43,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨44,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨45,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨46,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨47,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨48,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨49,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨50,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨51,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12832) (by norm_num)
        (q := 1 - (cell12832 ⟨52,by decide⟩).lower)
        (by norm_num [cell12832]) (by norm_num [cell12832])
      exact ⟨E.1,E.2.trans (by norm_num [cell12832])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12832

/-! Source-cell containment and simple scalar guards at 12832. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12832)
open BstLean.Part268 (cell12832)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12832 ⟨10,by decide⟩).lower ∧ (cell12832 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12832 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12832 ⟨11,by decide⟩).lower ∧ (cell12832 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12832 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12832 ⟨12,by decide⟩).lower ∧ (cell12832 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12832 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12832 ⟨13,by decide⟩).lower ∧ (cell12832 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12832 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12832 ⟨14,by decide⟩).lower ∧ (cell12832 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12832 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12832 ⟨15,by decide⟩).lower ∧ (cell12832 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12832 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12832 ⟨16,by decide⟩).lower ∧ (cell12832 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12832 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12832 ⟨17,by decide⟩).lower ∧ (cell12832 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12832 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12832 ⟨18,by decide⟩).lower ∧ (cell12832 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12832 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12832 ⟨19,by decide⟩).lower ∧ (cell12832 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12832 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12832 ⟨20,by decide⟩).lower ∧ (cell12832 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12832 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12832 ⟨21,by decide⟩).lower ∧ (cell12832 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12832 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12832 ⟨22,by decide⟩).lower ∧ (cell12832 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12832 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12832 ⟨23,by decide⟩).lower ∧ (cell12832 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12832 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12832 ⟨24,by decide⟩).lower ∧ (cell12832 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12832 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12832 ⟨25,by decide⟩).lower ∧ (cell12832 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12832 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12832 ⟨26,by decide⟩).lower ∧ (cell12832 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12832 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12832 ⟨27,by decide⟩).lower ∧ (cell12832 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12832 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12832 ⟨28,by decide⟩).lower ∧ (cell12832 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12832 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12832 ⟨29,by decide⟩).lower ∧ (cell12832 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12832 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12832 ⟨30,by decide⟩).lower ∧ (cell12832 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12832 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12832 ⟨31,by decide⟩).lower ∧ (cell12832 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12832 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12832 ⟨32,by decide⟩).lower ∧ (cell12832 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12832 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12832 ⟨33,by decide⟩).lower ∧ (cell12832 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12832 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12832 ⟨34,by decide⟩).lower ∧ (cell12832 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12832 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12832 ⟨35,by decide⟩).lower ∧ (cell12832 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12832 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12832 ⟨36,by decide⟩).lower ∧ (cell12832 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12832 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12832 ⟨37,by decide⟩).lower ∧ (cell12832 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12832 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12832 ⟨38,by decide⟩).lower ∧ (cell12832 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12832 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12832 ⟨39,by decide⟩).lower ∧ (cell12832 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12832 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12832 ⟨40,by decide⟩).lower ∧ (cell12832 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12832 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12832 ⟨41,by decide⟩).lower ∧ (cell12832 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12832 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12832 ⟨42,by decide⟩).lower ∧ (cell12832 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12832 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12832 ⟨43,by decide⟩).lower ∧ (cell12832 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12832 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12832 ⟨44,by decide⟩).lower ∧ (cell12832 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12832 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12832 ⟨45,by decide⟩).lower ∧ (cell12832 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12832 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12832 ⟨46,by decide⟩).lower ∧ (cell12832 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12832 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12832 ⟨47,by decide⟩).lower ∧ (cell12832 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12832 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12832 ⟨48,by decide⟩).lower ∧ (cell12832 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12832 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12832 ⟨49,by decide⟩).lower ∧ (cell12832 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12832 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12832 ⟨50,by decide⟩).lower ∧ (cell12832 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12832 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12832 ⟨51,by decide⟩).lower ∧ (cell12832 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12832 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12832 ⟨52,by decide⟩).lower ∧ (cell12832 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12832 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12832 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12832 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12832,cell12832,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12832 i).lower ∧
    (cell12832 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12832 i).upper ≤ (0.532 : ℝ) ∧
    (cell12832 i).centre ≤ (0.1 : ℝ) ∧ (cell12832 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12832 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12832 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12832

/-! The local source numeric instances at 12832 have no network premises. -/
namespace BstLean.Part269.N12832
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12832)
open BstLean.Part268 (cell12832)

noncomputable def sourceNumerics12832 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12832 (cell12832 i)
      scalarRow12832.M scalarRow12832.H scalarRow12832.xi := by
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
    energy_allowance := scalarRow12832.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12832]
    centre_nonneg := (scalarRow12832.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12832])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12832
/-! Actual 12833 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12833 ≤ (1.035621548161 : ℝ) := by
  have hr : (113.282831885506 : ℝ) ≤ √(12833 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.282831885506 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12833 12833 (11 / 1000) ≤
    (0.008438056986 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12833) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.282831885506 : ℝ) ≤ √(12833 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12833)
  have hdiv : K / √(12833 : ℝ) ≤ K / 113.282831885506 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.282831885506 ≤ (0.008438056986 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12833.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12833 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12833 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12833 := gPlus_lower 12833
end BstLean.Part269.N12833

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12833
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035621548160 : ℝ) ≤ wn 12833 := by
  have hn : √(12833 : ℝ) ≤ 113.282831885507 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12833 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.282831885507 ≤ 2 / √(12833 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249225235 : ℝ) ≤ rhoBar 12833 BstLean.Part154.csC ∧
    rhoBar 12833 BstLean.Part154.csC ≤ 0.000249225621 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035621548160 : ℝ) / (1.295212 * 12833) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035621548161 : ℝ) / (1.29521 * 12833) := by gcongr
      _ ≤ (0.000249225621 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12833 BstLean.Part154.csC) ≤ 0.000996964598 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12833 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) ≤ 0.000190360117 ∧
    cc1 (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) ≤ 0.000121127426 ∧
    cc2 (rhoBar 12833 BstLean.Part154.csC) ≤ 0.000070315422 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12833 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12833 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12833 BstLean.Part154.csC * nuR (rhoBar 12833 BstLean.Part154.csC)) ≤ 0.000498466771 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249225621 : ℝ) * 0.000996964598 := by gcongr
      _ ≤ (0.000498466771 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12833 BstLean.Part154.csC) * nuR (rhoBar 12833 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996964598 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12833 BstLean.Part154.csC) * rhoBar 12833 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249225621 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249225621 / 2 + 0.399 * 0.000996964598 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190360117 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498466771 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121127426 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249225621 / 1.414213562 := by gcongr
      _ ≤ (0.000070315422 : ℝ) := by norm_num

end BstLean.Part269.N12833

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12833
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) ≤ 1.56490E-7 := by
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12833 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12833 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12833 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190360117 : ℝ) ^ 2 + 0.000121127426 ^ 2 + 3 * 0.000070315422 ^ 2 +
        2 * 0.797885 * 0.000190360117 * 0.000121127426 + 2 * 0.000190360117 * 0.000070315422 +
        4 * 0.797885 * 0.000121127426 * 0.000070315422 := by gcongr
    _ ≤ (1.56490E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12833 BstLean.Part154.csC Θ ≤ 0.002601091597 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12833 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12833 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12833 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035621548161 * 1.56490E-7 / (0.000249225235 : ℝ) := by gcongr
    _ ≤ 0.002601091597 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12833 BstLean.Part154.csC Θ ≤ 0.002885532061 + 0.000657255108 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12833 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12833 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035621548161 : ℝ) * ((2 * Θ * 0.000249225621 +
        (6863 / 10000) * 0.000249225621 * 12833 * 0.000996964598) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002885532061 + 0.000657255108 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12833 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12833 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12833 0.011 Θ ∧ gammaRatio 12833 0.011 Θ ≤ 0.000085677324 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12833 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035621548161 : ℝ) * 0.525 / ((1 - 0.011) * 12833) := by gcongr
      _ ≤ (0.000085677324 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12833 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12833 0.011 Θ) :=
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
    badAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12833 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12833 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12833 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12833 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12833 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12833 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12833 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12833 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12833 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12833 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035621548161 : ℝ) * 12833 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003395194277 + 0.003258346705 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12833

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12833
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12833 BstLean.Part154.csC) (piBar (rhoBar 12833 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12833 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12833 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12833 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12833 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12833 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12833 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12833 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12833 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12833 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12833 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052208691792 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12833) ≤ 0.010542087987 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12833 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035621548161)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010542087987 + 2 * 0.737676 / 12833) := by gcongr
    _ ≤ (0.052208691792 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12833 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12833

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12833
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509520610 : ℝ) ≤ plow 12833 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12833) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612426298)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365573089) : eMP 12833 0.011 xi bn ≤ 0.001175810136 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12833 : ℝ) * (1 - 0.011))) ≤ 0.000581393527 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365573089 / (12833 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581393527 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581393527 : ℝ) + 3.141593 * 0.052612426298 / (12833 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175810136 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612426298)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365573089) : PiBarMP 12833 12 0.011 xi bn ≤ 0.160404795845 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12833 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036953661375 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.658053418297 : ℝ) ≤ √((12833 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.282831885506 : ℝ) ≤ √(12833 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12833) ≤ 0.122987817579 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036953661375 + 0.052612426298 * 1.772454 / (2 * (112.658053418297 : ℝ))) * (1 + 0.001175810136) +
        8 / (12833 * 113.282831885506) + 0.122987817579 := by gcongr
    _ ≤ (0.160404795845 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612426298)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365573089) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281582679633) :
    parallelOracle 12833 0.011 xi bn cd ≤ 0.161384824590 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12833 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12833 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509520610 : ℝ) ≤ plow 12833 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.282831885506 : ℝ) ≤ √(12833 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281582679633 : ℝ) / (2 * 0.560509520610 * 113.282831885506)) * 0.160404795845 +
        0.281582679633 ^ 2 / (2 * 0.560509520610 * 113.282831885506) := by gcongr
    _ ≤ (0.161384824590 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612426298) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365573089)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281582679633) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12833 12833 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509520610 : ℝ) ≤ plow 12833 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.282831885506 : ℝ) ≤ √(12833 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12833 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12833 Θ 1.22 ≤ 0.011706103017 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.282831885506 := by gcongr <;> linarith
      _ ≤ (0.011706103017 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12833 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12833 12833 0.011 ≤ 0.008438056986 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12833 12833 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12833 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12833 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12833 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12833 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161384824590 + 0.011706103017 + (0.008438056986 : ℝ) *
        (1 + 2 * (0.281582679633 + 0.011706103017) / (0.560509520610 * 113.282831885506))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12833]

end BstLean.Part269.N12833

/-! The original eight local profiles supply actual 12833 moment certificates. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12833 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052612426298 ∧
    0 ≤ bN 12833 BstLean.Part154.csC (groupTheta g) ∧ bN 12833 BstLean.Part154.csC (groupTheta g) ≤ 0.001365573089 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12833 12833 0.011
      (momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12833 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12833 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12833 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229373987841 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12833 0.011
      (momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12833 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12833
/-! The actual computed-centre upper energy formula at 12833. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12833

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12833)
open BstLean.Part268 (cell12833)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085111563298
  | 2 => 0.086047558458
  | 3 => 0.086980741134
  | 4 => 0.087912307787
  | 5 => 0.088843712537
  | 6 => 0.089776706311
  | 7 => 0.090713379846
  | 8 => 0.091656210606
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12833 12833 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12833 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12833

/-! Actual upper energy certificates on all 43 source endpoints at 12833. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12833)
open BstLean.Part268 (cell12833)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12833 (gMinus 12833) (1 - (cell12833 i).lower) ≤ 1 ∧
    energyUpper 12833 (gMinus 12833) (BstLean.Part211.gPlus 12833)
      (finiteEnergy 12833 12833 0.011) (1 - (cell12833 i).lower) ≤
      (cell12833 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨10,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨11,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨12,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨13,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨14,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨15,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨16,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨17,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨18,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨19,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨20,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨21,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨22,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨23,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨24,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨25,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨26,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨27,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨28,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨29,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨30,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨31,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨32,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨33,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨34,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨35,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨36,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨37,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨38,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨39,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨40,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨41,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨42,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨43,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨44,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨45,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨46,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨47,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨48,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨49,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨50,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨51,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12833) (by norm_num)
        (q := 1 - (cell12833 ⟨52,by decide⟩).lower)
        (by norm_num [cell12833]) (by norm_num [cell12833])
      exact ⟨E.1,E.2.trans (by norm_num [cell12833])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12833

/-! Source-cell containment and simple scalar guards at 12833. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12833)
open BstLean.Part268 (cell12833)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12833 ⟨10,by decide⟩).lower ∧ (cell12833 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12833 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12833 ⟨11,by decide⟩).lower ∧ (cell12833 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12833 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12833 ⟨12,by decide⟩).lower ∧ (cell12833 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12833 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12833 ⟨13,by decide⟩).lower ∧ (cell12833 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12833 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12833 ⟨14,by decide⟩).lower ∧ (cell12833 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12833 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12833 ⟨15,by decide⟩).lower ∧ (cell12833 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12833 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12833 ⟨16,by decide⟩).lower ∧ (cell12833 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12833 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12833 ⟨17,by decide⟩).lower ∧ (cell12833 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12833 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12833 ⟨18,by decide⟩).lower ∧ (cell12833 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12833 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12833 ⟨19,by decide⟩).lower ∧ (cell12833 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12833 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12833 ⟨20,by decide⟩).lower ∧ (cell12833 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12833 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12833 ⟨21,by decide⟩).lower ∧ (cell12833 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12833 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12833 ⟨22,by decide⟩).lower ∧ (cell12833 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12833 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12833 ⟨23,by decide⟩).lower ∧ (cell12833 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12833 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12833 ⟨24,by decide⟩).lower ∧ (cell12833 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12833 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12833 ⟨25,by decide⟩).lower ∧ (cell12833 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12833 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12833 ⟨26,by decide⟩).lower ∧ (cell12833 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12833 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12833 ⟨27,by decide⟩).lower ∧ (cell12833 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12833 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12833 ⟨28,by decide⟩).lower ∧ (cell12833 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12833 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12833 ⟨29,by decide⟩).lower ∧ (cell12833 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12833 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12833 ⟨30,by decide⟩).lower ∧ (cell12833 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12833 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12833 ⟨31,by decide⟩).lower ∧ (cell12833 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12833 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12833 ⟨32,by decide⟩).lower ∧ (cell12833 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12833 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12833 ⟨33,by decide⟩).lower ∧ (cell12833 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12833 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12833 ⟨34,by decide⟩).lower ∧ (cell12833 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12833 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12833 ⟨35,by decide⟩).lower ∧ (cell12833 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12833 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12833 ⟨36,by decide⟩).lower ∧ (cell12833 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12833 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12833 ⟨37,by decide⟩).lower ∧ (cell12833 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12833 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12833 ⟨38,by decide⟩).lower ∧ (cell12833 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12833 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12833 ⟨39,by decide⟩).lower ∧ (cell12833 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12833 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12833 ⟨40,by decide⟩).lower ∧ (cell12833 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12833 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12833 ⟨41,by decide⟩).lower ∧ (cell12833 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12833 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12833 ⟨42,by decide⟩).lower ∧ (cell12833 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12833 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12833 ⟨43,by decide⟩).lower ∧ (cell12833 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12833 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12833 ⟨44,by decide⟩).lower ∧ (cell12833 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12833 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12833 ⟨45,by decide⟩).lower ∧ (cell12833 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12833 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12833 ⟨46,by decide⟩).lower ∧ (cell12833 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12833 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12833 ⟨47,by decide⟩).lower ∧ (cell12833 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12833 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12833 ⟨48,by decide⟩).lower ∧ (cell12833 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12833 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12833 ⟨49,by decide⟩).lower ∧ (cell12833 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12833 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12833 ⟨50,by decide⟩).lower ∧ (cell12833 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12833 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12833 ⟨51,by decide⟩).lower ∧ (cell12833 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12833 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12833 ⟨52,by decide⟩).lower ∧ (cell12833 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12833 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12833 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12833 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12833,cell12833,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12833 i).lower ∧
    (cell12833 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12833 i).upper ≤ (0.532 : ℝ) ∧
    (cell12833 i).centre ≤ (0.1 : ℝ) ∧ (cell12833 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12833 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12833 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12833

/-! The local source numeric instances at 12833 have no network premises. -/
namespace BstLean.Part269.N12833
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12833)
open BstLean.Part268 (cell12833)

noncomputable def sourceNumerics12833 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12833 (cell12833 i)
      scalarRow12833.M scalarRow12833.H scalarRow12833.xi := by
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
    energy_allowance := scalarRow12833.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12833]
    centre_nonneg := (scalarRow12833.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12833])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12833
/-! Actual 12834 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12834 ≤ (1.035620148210 : ℝ) := by
  have hr : (113.287245530995 : ℝ) ≤ √(12834 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.287245530995 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12834 12834 (11 / 1000) ≤
    (0.008437728239 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12834) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.287245530995 : ℝ) ≤ √(12834 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12834)
  have hdiv : K / √(12834 : ℝ) ≤ K / 113.287245530995 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.287245530995 ≤ (0.008437728239 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12834.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12834 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12834 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12834 := gPlus_lower 12834
end BstLean.Part269.N12834

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12834
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035620148209 : ℝ) ≤ wn 12834 := by
  have hn : √(12834 : ℝ) ≤ 113.287245530996 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12834 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.287245530996 ≤ 2 / √(12834 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249205479 : ℝ) ≤ rhoBar 12834 BstLean.Part154.csC ∧
    rhoBar 12834 BstLean.Part154.csC ≤ 0.000249205865 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035620148209 : ℝ) / (1.295212 * 12834) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035620148210 : ℝ) / (1.29521 * 12834) := by gcongr
      _ ≤ (0.000249205865 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12834 BstLean.Part154.csC) ≤ 0.000996885564 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12834 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) ≤ 0.000190345027 ∧
    cc1 (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) ≤ 0.000121117824 ∧
    cc2 (rhoBar 12834 BstLean.Part154.csC) ≤ 0.000070309848 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12834 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12834 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12834 BstLean.Part154.csC * nuR (rhoBar 12834 BstLean.Part154.csC)) ≤ 0.000498427256 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249205865 : ℝ) * 0.000996885564 := by gcongr
      _ ≤ (0.000498427256 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12834 BstLean.Part154.csC) * nuR (rhoBar 12834 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996885564 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12834 BstLean.Part154.csC) * rhoBar 12834 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249205865 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249205865 / 2 + 0.399 * 0.000996885564 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190345027 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498427256 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121117824 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249205865 / 1.414213562 := by gcongr
      _ ≤ (0.000070309848 : ℝ) := by norm_num

end BstLean.Part269.N12834

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12834
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) ≤ 1.56466E-7 := by
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12834 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12834 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12834 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190345027 : ℝ) ^ 2 + 0.000121117824 ^ 2 + 3 * 0.000070309848 ^ 2 +
        2 * 0.797885 * 0.000190345027 * 0.000121117824 + 2 * 0.000190345027 * 0.000070309848 +
        4 * 0.797885 * 0.000121117824 * 0.000070309848 := by gcongr
    _ ≤ (1.56466E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12834 BstLean.Part154.csC Θ ≤ 0.002600895338 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12834 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12834 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12834 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035620148210 * 1.56466E-7 / (0.000249205479 : ℝ) := by gcongr
    _ ≤ 0.002600895338 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12834 BstLean.Part154.csC Θ ≤ 0.002885295512 + 0.000657202119 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12834 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12834 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035620148210 : ℝ) * ((2 * Θ * 0.000249205865 +
        (6863 / 10000) * 0.000249205865 * 12834 * 0.000996885564) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002885295512 + 0.000657202119 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12834 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12834 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12834 0.011 Θ ∧ gammaRatio 12834 0.011 Θ ≤ 0.000085670532 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12834 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035620148210 : ℝ) * 0.525 / ((1 - 0.011) * 12834) := by gcongr
      _ ≤ (0.000085670532 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12834 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12834 0.011 Θ) :=
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
    badAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12834 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12834 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12834 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12834 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12834 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12834 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12834 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12834 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12834 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12834 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035620148210 : ℝ) * 12834 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003394957728 + 0.003258097457 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12834

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12834
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12834 BstLean.Part154.csC) (piBar (rhoBar 12834 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12834 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12834 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12834 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12834 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12834 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12834 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12834 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12834 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12834 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12834 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052206635809 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12834) ≤ 0.010541677269 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12834 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035620148210)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010541677269 + 2 * 0.737676 / 12834) := by gcongr
    _ ≤ (0.052206635809 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12834 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12834

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12834
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509564897 : ℝ) ≤ plow 12834 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12834) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612058893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365470053) : eMP 12834 0.011 xi bn ≤ 0.001175719863 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12834 : ℝ) * (1 - 0.011))) ≤ 0.000581348943 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365470053 / (12834 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581348943 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581348943 : ℝ) + 3.141593 * 0.052612058893 / (12834 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175719863 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612058893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365470053) : PiBarMP 12834 12 0.011 xi bn ≤ 0.160398585425 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12834 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036952267225 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.662442721609 : ℝ) ≤ √((12834 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.287245530995 : ℝ) ≤ √(12834 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12834) ≤ 0.122983026002 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036952267225 + 0.052612058893 * 1.772454 / (2 * (112.662442721609 : ℝ))) * (1 + 0.001175719863) +
        8 / (12834 * 113.287245530995) + 0.122983026002 := by gcongr
    _ ≤ (0.160398585425 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612058893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365470053) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281579822763) :
    parallelOracle 12834 0.011 xi bn cd ≤ 0.161378545864 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12834 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12834 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509564897 : ℝ) ≤ plow 12834 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.287245530995 : ℝ) ≤ √(12834 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281579822763 : ℝ) / (2 * 0.560509564897 * 113.287245530995)) * 0.160398585425 +
        0.281579822763 ^ 2 / (2 * 0.560509564897 * 113.287245530995) := by gcongr
    _ ≤ (0.161378545864 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052612058893) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365470053)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281579822763) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12834 12834 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509564897 : ℝ) ≤ plow 12834 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.287245530995 : ℝ) ≤ √(12834 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12834 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12834 Θ 1.22 ≤ 0.011705646949 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.287245530995 := by gcongr <;> linarith
      _ ≤ (0.011705646949 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12834 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12834 12834 0.011 ≤ 0.008437728239 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12834 12834 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12834 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12834 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12834 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12834 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161378545864 + 0.011705646949 + (0.008437728239 : ℝ) *
        (1 + 2 * (0.281579822763 + 0.011705646949) / (0.560509564897 * 113.287245530995))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12834]

end BstLean.Part269.N12834

/-! The original eight local profiles supply actual 12834 moment certificates. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12834 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052612058893 ∧
    0 ≤ bN 12834 BstLean.Part154.csC (groupTheta g) ∧ bN 12834 BstLean.Part154.csC (groupTheta g) ≤ 0.001365470053 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12834 12834 0.011
      (momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12834 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12834 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12834 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229373186954 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12834 0.011
      (momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12834 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12834
/-! The actual computed-centre upper energy formula at 12834. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12834

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12834)
open BstLean.Part268 (cell12834)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085108782464
  | 2 => 0.086044729500
  | 3 => 0.086977857518
  | 4 => 0.087909361444
  | 5 => 0.088840693581
  | 6 => 0.089773602730
  | 7 => 0.090710177150
  | 8 => 0.091652891441
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12834 12834 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12834 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12834

/-! Actual upper energy certificates on all 43 source endpoints at 12834. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12834)
open BstLean.Part268 (cell12834)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12834 (gMinus 12834) (1 - (cell12834 i).lower) ≤ 1 ∧
    energyUpper 12834 (gMinus 12834) (BstLean.Part211.gPlus 12834)
      (finiteEnergy 12834 12834 0.011) (1 - (cell12834 i).lower) ≤
      (cell12834 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨10,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨11,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨12,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨13,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨14,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨15,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨16,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨17,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨18,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨19,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨20,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨21,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨22,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨23,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨24,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨25,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨26,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨27,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨28,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨29,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨30,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨31,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨32,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨33,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨34,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨35,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨36,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨37,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨38,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨39,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨40,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨41,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨42,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨43,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨44,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨45,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨46,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨47,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨48,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨49,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨50,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨51,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12834) (by norm_num)
        (q := 1 - (cell12834 ⟨52,by decide⟩).lower)
        (by norm_num [cell12834]) (by norm_num [cell12834])
      exact ⟨E.1,E.2.trans (by norm_num [cell12834])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12834

/-! Source-cell containment and simple scalar guards at 12834. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12834)
open BstLean.Part268 (cell12834)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12834 ⟨10,by decide⟩).lower ∧ (cell12834 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12834 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12834 ⟨11,by decide⟩).lower ∧ (cell12834 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12834 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12834 ⟨12,by decide⟩).lower ∧ (cell12834 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12834 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12834 ⟨13,by decide⟩).lower ∧ (cell12834 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12834 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12834 ⟨14,by decide⟩).lower ∧ (cell12834 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12834 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12834 ⟨15,by decide⟩).lower ∧ (cell12834 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12834 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12834 ⟨16,by decide⟩).lower ∧ (cell12834 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12834 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12834 ⟨17,by decide⟩).lower ∧ (cell12834 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12834 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12834 ⟨18,by decide⟩).lower ∧ (cell12834 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12834 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12834 ⟨19,by decide⟩).lower ∧ (cell12834 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12834 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12834 ⟨20,by decide⟩).lower ∧ (cell12834 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12834 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12834 ⟨21,by decide⟩).lower ∧ (cell12834 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12834 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12834 ⟨22,by decide⟩).lower ∧ (cell12834 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12834 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12834 ⟨23,by decide⟩).lower ∧ (cell12834 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12834 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12834 ⟨24,by decide⟩).lower ∧ (cell12834 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12834 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12834 ⟨25,by decide⟩).lower ∧ (cell12834 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12834 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12834 ⟨26,by decide⟩).lower ∧ (cell12834 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12834 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12834 ⟨27,by decide⟩).lower ∧ (cell12834 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12834 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12834 ⟨28,by decide⟩).lower ∧ (cell12834 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12834 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12834 ⟨29,by decide⟩).lower ∧ (cell12834 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12834 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12834 ⟨30,by decide⟩).lower ∧ (cell12834 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12834 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12834 ⟨31,by decide⟩).lower ∧ (cell12834 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12834 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12834 ⟨32,by decide⟩).lower ∧ (cell12834 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12834 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12834 ⟨33,by decide⟩).lower ∧ (cell12834 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12834 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12834 ⟨34,by decide⟩).lower ∧ (cell12834 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12834 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12834 ⟨35,by decide⟩).lower ∧ (cell12834 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12834 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12834 ⟨36,by decide⟩).lower ∧ (cell12834 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12834 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12834 ⟨37,by decide⟩).lower ∧ (cell12834 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12834 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12834 ⟨38,by decide⟩).lower ∧ (cell12834 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12834 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12834 ⟨39,by decide⟩).lower ∧ (cell12834 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12834 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12834 ⟨40,by decide⟩).lower ∧ (cell12834 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12834 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12834 ⟨41,by decide⟩).lower ∧ (cell12834 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12834 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12834 ⟨42,by decide⟩).lower ∧ (cell12834 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12834 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12834 ⟨43,by decide⟩).lower ∧ (cell12834 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12834 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12834 ⟨44,by decide⟩).lower ∧ (cell12834 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12834 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12834 ⟨45,by decide⟩).lower ∧ (cell12834 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12834 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12834 ⟨46,by decide⟩).lower ∧ (cell12834 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12834 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12834 ⟨47,by decide⟩).lower ∧ (cell12834 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12834 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12834 ⟨48,by decide⟩).lower ∧ (cell12834 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12834 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12834 ⟨49,by decide⟩).lower ∧ (cell12834 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12834 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12834 ⟨50,by decide⟩).lower ∧ (cell12834 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12834 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12834 ⟨51,by decide⟩).lower ∧ (cell12834 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12834 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12834 ⟨52,by decide⟩).lower ∧ (cell12834 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12834 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12834 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12834 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12834,cell12834,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12834 i).lower ∧
    (cell12834 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12834 i).upper ≤ (0.532 : ℝ) ∧
    (cell12834 i).centre ≤ (0.1 : ℝ) ∧ (cell12834 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12834 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12834 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12834

/-! The local source numeric instances at 12834 have no network premises. -/
namespace BstLean.Part269.N12834
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12834)
open BstLean.Part268 (cell12834)

noncomputable def sourceNumerics12834 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12834 (cell12834 i)
      scalarRow12834.M scalarRow12834.H scalarRow12834.xi := by
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
    energy_allowance := scalarRow12834.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12834]
    centre_nonneg := (scalarRow12834.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12834])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12834
/-! Actual 12835 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12835 ≤ (1.035618748424 : ℝ) := by
  have hr : (113.291659004535 : ℝ) ≤ √(12835 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.291659004535 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12835 12835 (11 / 1000) ≤
    (0.008437399530 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12835) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.291659004535 : ℝ) ≤ √(12835 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12835)
  have hdiv : K / √(12835 : ℝ) ≤ K / 113.291659004535 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.291659004535 ≤ (0.008437399530 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12835.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12835 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12835 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12835 := gPlus_lower 12835
end BstLean.Part269.N12835

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12835
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035618748423 : ℝ) ≤ wn 12835 := by
  have hn : √(12835 : ℝ) ≤ 113.291659004536 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12835 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.291659004536 ≤ 2 / √(12835 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249185727 : ℝ) ≤ rhoBar 12835 BstLean.Part154.csC ∧
    rhoBar 12835 BstLean.Part154.csC ≤ 0.000249186112 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035618748423 : ℝ) / (1.295212 * 12835) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035618748424 : ℝ) / (1.29521 * 12835) := by gcongr
      _ ≤ (0.000249186112 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12835 BstLean.Part154.csC) ≤ 0.000996806542 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12835 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) ≤ 0.000190329939 ∧
    cc1 (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) ≤ 0.000121108223 ∧
    cc2 (rhoBar 12835 BstLean.Part154.csC) ≤ 0.000070304275 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12835 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12835 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12835 BstLean.Part154.csC * nuR (rhoBar 12835 BstLean.Part154.csC)) ≤ 0.000498387748 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249186112 : ℝ) * 0.000996806542 := by gcongr
      _ ≤ (0.000498387748 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12835 BstLean.Part154.csC) * nuR (rhoBar 12835 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996806542 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12835 BstLean.Part154.csC) * rhoBar 12835 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249186112 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249186112 / 2 + 0.399 * 0.000996806542 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190329939 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498387748 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121108223 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249186112 / 1.414213562 := by gcongr
      _ ≤ (0.000070304275 : ℝ) := by norm_num

end BstLean.Part269.N12835

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12835
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) ≤ 1.56441E-7 := by
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12835 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12835 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12835 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190329939 : ℝ) ^ 2 + 0.000121108223 ^ 2 + 3 * 0.000070304275 ^ 2 +
        2 * 0.797885 * 0.000190329939 * 0.000121108223 + 2 * 0.000190329939 * 0.000070304275 +
        4 * 0.797885 * 0.000121108223 * 0.000070304275 := by gcongr
    _ ≤ (1.56441E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12835 BstLean.Part154.csC Θ ≤ 0.002600682384 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12835 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12835 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12835 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035618748424 * 1.56441E-7 / (0.000249185727 : ℝ) := by gcongr
    _ ≤ 0.002600682384 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12835 BstLean.Part154.csC Θ ≤ 0.002885058997 + 0.000657149139 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12835 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12835 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035618748424 : ℝ) * ((2 * Θ * 0.000249186112 +
        (6863 / 10000) * 0.000249186112 * 12835 * 0.000996806542) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002885058997 + 0.000657149139 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12835 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12835 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12835 0.011 Θ ∧ gammaRatio 12835 0.011 Θ ≤ 0.000085663742 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12835 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035618748424 : ℝ) * 0.525 / ((1 - 0.011) * 12835) := by gcongr
      _ ≤ (0.000085663742 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12835 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12835 0.011 Θ) :=
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
    badAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12835 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12835 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12835 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12835 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12835 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12835 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12835 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12835 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12835 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12835 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035618748424 : ℝ) * 12835 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003394721213 + 0.003257831523 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12835

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12835
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12835 BstLean.Part154.csC) (piBar (rhoBar 12835 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12835 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12835 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12835 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12835 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12835 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12835 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12835 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12835 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12835 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12835 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052204580072 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12835) ≤ 0.010541266600 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12835 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035618748424)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010541266600 + 2 * 0.737676 / 12835) := by gcongr
    _ ≤ (0.052204580072 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12835 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12835

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12835
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509609178 : ℝ) ≤ plow 12835 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12835) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611682763)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365358252) : eMP 12835 0.011 xi bn ≤ 0.001175625861 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12835 : ℝ) * (1 - 0.011))) ≤ 0.000581302496 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365358252 / (12835 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581302496 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581302496 : ℝ) + 3.141593 * 0.052611682763 / (12835 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175625861 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611682763)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365358252) : PiBarMP 12835 12 0.011 xi bn ≤ 0.160392256562 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12835 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036950754418 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.666831853922 : ℝ) ≤ √((12835 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.291659004535 : ℝ) ≤ √(12835 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12835) ≤ 0.122978234984 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036950754418 + 0.052611682763 * 1.772454 / (2 * (112.666831853922 : ℝ))) * (1 + 0.001175625861) +
        8 / (12835 * 113.291659004535) + 0.122978234984 := by gcongr
    _ ≤ (0.160392256562 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611682763)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365358252) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281576947116) :
    parallelOracle 12835 0.011 xi bn cd ≤ 0.161372148333 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12835 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12835 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509609178 : ℝ) ≤ plow 12835 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.291659004535 : ℝ) ≤ √(12835 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281576947116 : ℝ) / (2 * 0.560509609178 * 113.291659004535)) * 0.160392256562 +
        0.281576947116 ^ 2 / (2 * 0.560509609178 * 113.291659004535) := by gcongr
    _ ≤ (0.161372148333 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611682763) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365358252)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281576947116) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12835 12835 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509609178 : ℝ) ≤ plow 12835 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.291659004535 : ℝ) ≤ √(12835 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12835 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12835 Θ 1.22 ≤ 0.011705190936 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.291659004535 := by gcongr <;> linarith
      _ ≤ (0.011705190936 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12835 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12835 12835 0.011 ≤ 0.008437399530 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12835 12835 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12835 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12835 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12835 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12835 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161372148333 + 0.011705190936 + (0.008437399530 : ℝ) *
        (1 + 2 * (0.281576947116 + 0.011705190936) / (0.560509609178 * 113.291659004535))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12835]

end BstLean.Part269.N12835

/-! The original eight local profiles supply actual 12835 moment certificates. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12835 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052611682763 ∧
    0 ≤ bN 12835 BstLean.Part154.csC (groupTheta g) ∧ bN 12835 BstLean.Part154.csC (groupTheta g) ≤ 0.001365358252 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12835 12835 0.011
      (momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12835 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12835 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12835 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229372367044 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12835 0.011
      (momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12835 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12835
/-! The actual computed-centre upper energy formula at 12835. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12835

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12835)
open BstLean.Part268 (cell12835)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085106002578
  | 2 => 0.086041901528
  | 3 => 0.086974974935
  | 4 => 0.087906416190
  | 5 => 0.088837675784
  | 6 => 0.089770500393
  | 7 => 0.090706975802
  | 8 => 0.091649573745
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12835 12835 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12835 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12835

/-! Actual upper energy certificates on all 43 source endpoints at 12835. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12835)
open BstLean.Part268 (cell12835)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12835 (gMinus 12835) (1 - (cell12835 i).lower) ≤ 1 ∧
    energyUpper 12835 (gMinus 12835) (BstLean.Part211.gPlus 12835)
      (finiteEnergy 12835 12835 0.011) (1 - (cell12835 i).lower) ≤
      (cell12835 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨10,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨11,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨12,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨13,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨14,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨15,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨16,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨17,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨18,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨19,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨20,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨21,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨22,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨23,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨24,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨25,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨26,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨27,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨28,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨29,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨30,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨31,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨32,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨33,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨34,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨35,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨36,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨37,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨38,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨39,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨40,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨41,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨42,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨43,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨44,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨45,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨46,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨47,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨48,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨49,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨50,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨51,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12835) (by norm_num)
        (q := 1 - (cell12835 ⟨52,by decide⟩).lower)
        (by norm_num [cell12835]) (by norm_num [cell12835])
      exact ⟨E.1,E.2.trans (by norm_num [cell12835])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12835

/-! Source-cell containment and simple scalar guards at 12835. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12835)
open BstLean.Part268 (cell12835)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12835 ⟨10,by decide⟩).lower ∧ (cell12835 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12835 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12835 ⟨11,by decide⟩).lower ∧ (cell12835 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12835 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12835 ⟨12,by decide⟩).lower ∧ (cell12835 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12835 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12835 ⟨13,by decide⟩).lower ∧ (cell12835 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12835 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12835 ⟨14,by decide⟩).lower ∧ (cell12835 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12835 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12835 ⟨15,by decide⟩).lower ∧ (cell12835 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12835 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12835 ⟨16,by decide⟩).lower ∧ (cell12835 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12835 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12835 ⟨17,by decide⟩).lower ∧ (cell12835 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12835 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12835 ⟨18,by decide⟩).lower ∧ (cell12835 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12835 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12835 ⟨19,by decide⟩).lower ∧ (cell12835 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12835 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12835 ⟨20,by decide⟩).lower ∧ (cell12835 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12835 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12835 ⟨21,by decide⟩).lower ∧ (cell12835 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12835 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12835 ⟨22,by decide⟩).lower ∧ (cell12835 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12835 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12835 ⟨23,by decide⟩).lower ∧ (cell12835 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12835 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12835 ⟨24,by decide⟩).lower ∧ (cell12835 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12835 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12835 ⟨25,by decide⟩).lower ∧ (cell12835 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12835 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12835 ⟨26,by decide⟩).lower ∧ (cell12835 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12835 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12835 ⟨27,by decide⟩).lower ∧ (cell12835 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12835 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12835 ⟨28,by decide⟩).lower ∧ (cell12835 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12835 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12835 ⟨29,by decide⟩).lower ∧ (cell12835 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12835 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12835 ⟨30,by decide⟩).lower ∧ (cell12835 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12835 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12835 ⟨31,by decide⟩).lower ∧ (cell12835 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12835 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12835 ⟨32,by decide⟩).lower ∧ (cell12835 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12835 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12835 ⟨33,by decide⟩).lower ∧ (cell12835 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12835 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12835 ⟨34,by decide⟩).lower ∧ (cell12835 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12835 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12835 ⟨35,by decide⟩).lower ∧ (cell12835 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12835 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12835 ⟨36,by decide⟩).lower ∧ (cell12835 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12835 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12835 ⟨37,by decide⟩).lower ∧ (cell12835 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12835 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12835 ⟨38,by decide⟩).lower ∧ (cell12835 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12835 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12835 ⟨39,by decide⟩).lower ∧ (cell12835 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12835 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12835 ⟨40,by decide⟩).lower ∧ (cell12835 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12835 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12835 ⟨41,by decide⟩).lower ∧ (cell12835 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12835 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12835 ⟨42,by decide⟩).lower ∧ (cell12835 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12835 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12835 ⟨43,by decide⟩).lower ∧ (cell12835 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12835 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12835 ⟨44,by decide⟩).lower ∧ (cell12835 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12835 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12835 ⟨45,by decide⟩).lower ∧ (cell12835 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12835 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12835 ⟨46,by decide⟩).lower ∧ (cell12835 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12835 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12835 ⟨47,by decide⟩).lower ∧ (cell12835 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12835 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12835 ⟨48,by decide⟩).lower ∧ (cell12835 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12835 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12835 ⟨49,by decide⟩).lower ∧ (cell12835 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12835 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12835 ⟨50,by decide⟩).lower ∧ (cell12835 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12835 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12835 ⟨51,by decide⟩).lower ∧ (cell12835 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12835 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12835 ⟨52,by decide⟩).lower ∧ (cell12835 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12835 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12835 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12835 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12835,cell12835,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12835 i).lower ∧
    (cell12835 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12835 i).upper ≤ (0.532 : ℝ) ∧
    (cell12835 i).centre ≤ (0.1 : ℝ) ∧ (cell12835 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12835 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12835 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12835

/-! The local source numeric instances at 12835 have no network premises. -/
namespace BstLean.Part269.N12835
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12835)
open BstLean.Part268 (cell12835)

noncomputable def sourceNumerics12835 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12835 (cell12835 i)
      scalarRow12835.M scalarRow12835.H scalarRow12835.xi := by
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
    energy_allowance := scalarRow12835.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12835]
    centre_nonneg := (scalarRow12835.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12835])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12835
/-! Actual 12836 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12836 ≤ (1.035617348803 : ℝ) := by
  have hr : (113.296072306148 : ℝ) ≤ √(12836 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.296072306148 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12836 12836 (11 / 1000) ≤
    (0.008437070860 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12836) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.296072306148 : ℝ) ≤ √(12836 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12836)
  have hdiv : K / √(12836 : ℝ) ≤ K / 113.296072306148 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.296072306148 ≤ (0.008437070860 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12836.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12836 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12836 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12836 := gPlus_lower 12836
end BstLean.Part269.N12836

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12836
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035617348802 : ℝ) ≤ wn 12836 := by
  have hn : √(12836 : ℝ) ≤ 113.296072306149 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12836 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.296072306149 ≤ 2 / √(12836 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249165977 : ℝ) ≤ rhoBar 12836 BstLean.Part154.csC ∧
    rhoBar 12836 BstLean.Part154.csC ≤ 0.000249166363 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035617348802 : ℝ) / (1.295212 * 12836) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035617348803 : ℝ) / (1.29521 * 12836) := by gcongr
      _ ≤ (0.000249166363 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12836 BstLean.Part154.csC) ≤ 0.000996727536 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12836 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) ≤ 0.000190314853 ∧
    cc1 (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) ≤ 0.000121098625 ∧
    cc2 (rhoBar 12836 BstLean.Part154.csC) ≤ 0.000070298703 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12836 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12836 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12836 BstLean.Part154.csC * nuR (rhoBar 12836 BstLean.Part154.csC)) ≤ 0.000498348247 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249166363 : ℝ) * 0.000996727536 := by gcongr
      _ ≤ (0.000498348247 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12836 BstLean.Part154.csC) * nuR (rhoBar 12836 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996727536 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12836 BstLean.Part154.csC) * rhoBar 12836 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249166363 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249166363 / 2 + 0.399 * 0.000996727536 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190314853 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498348247 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121098625 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249166363 / 1.414213562 := by gcongr
      _ ≤ (0.000070298703 : ℝ) := by norm_num

end BstLean.Part269.N12836

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12836
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) ≤ 1.56416E-7 := by
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12836 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12836 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12836 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190314853 : ℝ) ^ 2 + 0.000121098625 ^ 2 + 3 * 0.000070298703 ^ 2 +
        2 * 0.797885 * 0.000190314853 * 0.000121098625 + 2 * 0.000190314853 * 0.000070298703 +
        4 * 0.797885 * 0.000121098625 * 0.000070298703 := by gcongr
    _ ≤ (1.56416E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12836 BstLean.Part154.csC Θ ≤ 0.002600469377 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12836 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12836 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12836 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035617348803 * 1.56416E-7 / (0.000249165977 : ℝ) := by gcongr
    _ ≤ 0.002600469377 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12836 BstLean.Part154.csC Θ ≤ 0.002884822542 + 0.000657096169 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12836 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12836 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035617348803 : ℝ) * ((2 * Θ * 0.000249166363 +
        (6863 / 10000) * 0.000249166363 * 12836 * 0.000996727536) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002884822542 + 0.000657096169 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12836 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12836 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12836 0.011 Θ ∧ gammaRatio 12836 0.011 Θ ≤ 0.000085656952 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12836 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035617348803 : ℝ) * 0.525 / ((1 - 0.011) * 12836) := by gcongr
      _ ≤ (0.000085656952 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12836 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12836 0.011 Θ) :=
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
    badAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12836 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12836 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12836 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12836 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12836 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12836 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12836 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12836 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12836 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12836 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035617348803 : ℝ) * 12836 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003394484758 + 0.003257565546 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12836

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12836
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12836 BstLean.Part154.csC) (piBar (rhoBar 12836 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12836 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12836 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12836 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12836 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12836 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12836 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12836 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12836 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12836 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12836 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052202524577 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12836) ≤ 0.010540855979 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12836 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035617348803)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010540855979 + 2 * 0.737676 / 12836) := by gcongr
    _ ≤ (0.052202524577 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12836 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12836

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12836
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509653451 : ℝ) ≤ plow 12836 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12836) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611306670)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365246423) : eMP 12836 0.011 xi bn ≤ 0.001175531855 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12836 : ℝ) * (1 - 0.011))) ≤ 0.000581256047 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365246423 / (12836 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581256047 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581256047 : ℝ) + 3.141593 * 0.052611306670 / (12836 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175531855 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611306670)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365246423) : PiBarMP 12836 12 0.011 xi bn ≤ 0.160385927821 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12836 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036949241170 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.671220815255 : ℝ) ≤ √((12836 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.296072306148 : ℝ) ≤ √(12836 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12836) ≤ 0.122973444526 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036949241170 + 0.052611306670 * 1.772454 / (2 * (112.671220815255 : ℝ))) * (1 + 0.001175531855) +
        8 / (12836 * 113.296072306148) + 0.122973444526 := by gcongr
    _ ≤ (0.160385927821 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611306670)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365246423) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281574071789) :
    parallelOracle 12836 0.011 xi bn cd ≤ 0.161365750933 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12836 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12836 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509653451 : ℝ) ≤ plow 12836 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.296072306148 : ℝ) ≤ √(12836 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281574071789 : ℝ) / (2 * 0.560509653451 * 113.296072306148)) * 0.160385927821 +
        0.281574071789 ^ 2 / (2 * 0.560509653451 * 113.296072306148) := by gcongr
    _ ≤ (0.161365750933 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052611306670) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365246423)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281574071789) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12836 12836 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509653451 : ℝ) ≤ plow 12836 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.296072306148 : ℝ) ≤ √(12836 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12836 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12836 Θ 1.22 ≤ 0.011704734975 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.296072306148 := by gcongr <;> linarith
      _ ≤ (0.011704734975 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12836 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12836 12836 0.011 ≤ 0.008437070860 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12836 12836 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12836 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12836 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12836 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12836 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161365750933 + 0.011704734975 + (0.008437070860 : ℝ) *
        (1 + 2 * (0.281574071789 + 0.011704734975) / (0.560509653451 * 113.296072306148))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12836]

end BstLean.Part269.N12836

/-! The original eight local profiles supply actual 12836 moment certificates. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12836 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052611306670 ∧
    0 ≤ bN 12836 BstLean.Part154.csC (groupTheta g) ∧ bN 12836 BstLean.Part154.csC (groupTheta g) ≤ 0.001365246423 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12836 12836 0.011
      (momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12836 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12836 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12836 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229371547212 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12836 0.011
      (momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12836 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12836
/-! The actual computed-centre upper energy formula at 12836. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12836

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12836)
open BstLean.Part268 (cell12836)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085103223640
  | 2 => 0.086039074542
  | 3 => 0.086972093384
  | 4 => 0.087903472024
  | 5 => 0.088834659145
  | 6 => 0.089767399298
  | 7 => 0.090703775798
  | 8 => 0.091646257518
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12836 12836 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12836 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12836

/-! Actual upper energy certificates on all 43 source endpoints at 12836. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12836)
open BstLean.Part268 (cell12836)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12836 (gMinus 12836) (1 - (cell12836 i).lower) ≤ 1 ∧
    energyUpper 12836 (gMinus 12836) (BstLean.Part211.gPlus 12836)
      (finiteEnergy 12836 12836 0.011) (1 - (cell12836 i).lower) ≤
      (cell12836 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨10,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨11,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨12,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨13,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨14,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨15,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨16,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨17,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨18,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨19,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨20,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨21,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨22,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨23,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨24,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨25,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨26,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨27,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨28,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨29,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨30,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨31,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨32,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨33,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨34,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨35,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨36,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨37,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨38,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨39,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨40,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨41,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨42,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨43,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨44,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨45,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨46,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨47,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨48,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨49,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨50,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨51,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12836) (by norm_num)
        (q := 1 - (cell12836 ⟨52,by decide⟩).lower)
        (by norm_num [cell12836]) (by norm_num [cell12836])
      exact ⟨E.1,E.2.trans (by norm_num [cell12836])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12836

/-! Source-cell containment and simple scalar guards at 12836. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12836)
open BstLean.Part268 (cell12836)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12836 ⟨10,by decide⟩).lower ∧ (cell12836 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12836 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12836 ⟨11,by decide⟩).lower ∧ (cell12836 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12836 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12836 ⟨12,by decide⟩).lower ∧ (cell12836 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12836 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12836 ⟨13,by decide⟩).lower ∧ (cell12836 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12836 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12836 ⟨14,by decide⟩).lower ∧ (cell12836 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12836 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12836 ⟨15,by decide⟩).lower ∧ (cell12836 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12836 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12836 ⟨16,by decide⟩).lower ∧ (cell12836 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12836 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12836 ⟨17,by decide⟩).lower ∧ (cell12836 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12836 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12836 ⟨18,by decide⟩).lower ∧ (cell12836 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12836 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12836 ⟨19,by decide⟩).lower ∧ (cell12836 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12836 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12836 ⟨20,by decide⟩).lower ∧ (cell12836 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12836 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12836 ⟨21,by decide⟩).lower ∧ (cell12836 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12836 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12836 ⟨22,by decide⟩).lower ∧ (cell12836 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12836 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12836 ⟨23,by decide⟩).lower ∧ (cell12836 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12836 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12836 ⟨24,by decide⟩).lower ∧ (cell12836 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12836 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12836 ⟨25,by decide⟩).lower ∧ (cell12836 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12836 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12836 ⟨26,by decide⟩).lower ∧ (cell12836 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12836 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12836 ⟨27,by decide⟩).lower ∧ (cell12836 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12836 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12836 ⟨28,by decide⟩).lower ∧ (cell12836 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12836 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12836 ⟨29,by decide⟩).lower ∧ (cell12836 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12836 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12836 ⟨30,by decide⟩).lower ∧ (cell12836 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12836 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12836 ⟨31,by decide⟩).lower ∧ (cell12836 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12836 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12836 ⟨32,by decide⟩).lower ∧ (cell12836 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12836 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12836 ⟨33,by decide⟩).lower ∧ (cell12836 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12836 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12836 ⟨34,by decide⟩).lower ∧ (cell12836 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12836 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12836 ⟨35,by decide⟩).lower ∧ (cell12836 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12836 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12836 ⟨36,by decide⟩).lower ∧ (cell12836 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12836 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12836 ⟨37,by decide⟩).lower ∧ (cell12836 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12836 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12836 ⟨38,by decide⟩).lower ∧ (cell12836 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12836 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12836 ⟨39,by decide⟩).lower ∧ (cell12836 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12836 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12836 ⟨40,by decide⟩).lower ∧ (cell12836 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12836 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12836 ⟨41,by decide⟩).lower ∧ (cell12836 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12836 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12836 ⟨42,by decide⟩).lower ∧ (cell12836 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12836 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12836 ⟨43,by decide⟩).lower ∧ (cell12836 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12836 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12836 ⟨44,by decide⟩).lower ∧ (cell12836 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12836 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12836 ⟨45,by decide⟩).lower ∧ (cell12836 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12836 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12836 ⟨46,by decide⟩).lower ∧ (cell12836 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12836 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12836 ⟨47,by decide⟩).lower ∧ (cell12836 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12836 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12836 ⟨48,by decide⟩).lower ∧ (cell12836 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12836 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12836 ⟨49,by decide⟩).lower ∧ (cell12836 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12836 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12836 ⟨50,by decide⟩).lower ∧ (cell12836 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12836 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12836 ⟨51,by decide⟩).lower ∧ (cell12836 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12836 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12836 ⟨52,by decide⟩).lower ∧ (cell12836 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12836 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12836 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12836 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12836,cell12836,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12836 i).lower ∧
    (cell12836 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12836 i).upper ≤ (0.532 : ℝ) ∧
    (cell12836 i).centre ≤ (0.1 : ℝ) ∧ (cell12836 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12836 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12836 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12836

/-! The local source numeric instances at 12836 have no network premises. -/
namespace BstLean.Part269.N12836
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12836)
open BstLean.Part268 (cell12836)

noncomputable def sourceNumerics12836 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12836 (cell12836 i)
      scalarRow12836.M scalarRow12836.H scalarRow12836.xi := by
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
    energy_allowance := scalarRow12836.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12836]
    centre_nonneg := (scalarRow12836.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12836])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12836
/-! Actual 12837 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12837 ≤ (1.035615949346 : ℝ) := by
  have hr : (113.300485435853 : ℝ) ≤ √(12837 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.300485435853 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12837 12837 (11 / 1000) ≤
    (0.008436742228 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12837) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.300485435853 : ℝ) ≤ √(12837 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12837)
  have hdiv : K / √(12837 : ℝ) ≤ K / 113.300485435853 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.300485435853 ≤ (0.008436742228 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12837.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12837 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12837 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12837 := gPlus_lower 12837
end BstLean.Part269.N12837

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12837
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035615949345 : ℝ) ≤ wn 12837 := by
  have hn : √(12837 : ℝ) ≤ 113.300485435854 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12837 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.300485435854 ≤ 2 / √(12837 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249146230 : ℝ) ≤ rhoBar 12837 BstLean.Part154.csC ∧
    rhoBar 12837 BstLean.Part154.csC ≤ 0.000249146616 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035615949345 : ℝ) / (1.295212 * 12837) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035615949346 : ℝ) / (1.29521 * 12837) := by gcongr
      _ ≤ (0.000249146616 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12837 BstLean.Part154.csC) ≤ 0.000996648539 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12837 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) ≤ 0.000190299770 ∧
    cc1 (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) ≤ 0.000121089027 ∧
    cc2 (rhoBar 12837 BstLean.Part154.csC) ≤ 0.000070293132 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12837 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12837 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12837 BstLean.Part154.csC * nuR (rhoBar 12837 BstLean.Part154.csC)) ≤ 0.000498308751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249146616 : ℝ) * 0.000996648539 := by gcongr
      _ ≤ (0.000498308751 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12837 BstLean.Part154.csC) * nuR (rhoBar 12837 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996648539 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12837 BstLean.Part154.csC) * rhoBar 12837 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249146616 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249146616 / 2 + 0.399 * 0.000996648539 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190299770 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498308751 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121089027 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249146616 / 1.414213562 := by gcongr
      _ ≤ (0.000070293132 : ℝ) := by norm_num

end BstLean.Part269.N12837

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12837
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) ≤ 1.56391E-7 := by
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12837 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12837 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12837 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190299770 : ℝ) ^ 2 + 0.000121089027 ^ 2 + 3 * 0.000070293132 ^ 2 +
        2 * 0.797885 * 0.000190299770 * 0.000121089027 + 2 * 0.000190299770 * 0.000070293132 +
        4 * 0.797885 * 0.000121089027 * 0.000070293132 := by gcongr
    _ ≤ (1.56391E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12837 BstLean.Part154.csC Θ ≤ 0.002600256307 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12837 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12837 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12837 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035615949346 * 1.56391E-7 / (0.000249146230 : ℝ) := by gcongr
    _ ≤ 0.002600256307 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12837 BstLean.Part154.csC Θ ≤ 0.002884586102 + 0.000657043205 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12837 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12837 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035615949346 : ℝ) * ((2 * Θ * 0.000249146616 +
        (6863 / 10000) * 0.000249146616 * 12837 * 0.000996648539) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002884586102 + 0.000657043205 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12837 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12837 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12837 0.011 Θ ∧ gammaRatio 12837 0.011 Θ ≤ 0.000085650164 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12837 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035615949346 : ℝ) * 0.525 / ((1 - 0.011) * 12837) := by gcongr
      _ ≤ (0.000085650164 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12837 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12837 0.011 Θ) :=
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
    badAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12837 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12837 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12837 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12837 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12837 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12837 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12837 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12837 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12837 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12837 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035615949346 : ℝ) * 12837 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003394248318 + 0.003257299512 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12837

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12837
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12837 BstLean.Part154.csC) (piBar (rhoBar 12837 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12837 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12837 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12837 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12837 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12837 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12837 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12837 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12837 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12837 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12837 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052200469319 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12837) ≤ 0.010540445405 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12837 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035615949346)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010540445405 + 2 * 0.737676 / 12837) := by gcongr
    _ ≤ (0.052200469319 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12837 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12837

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12837
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509697717 : ℝ) ≤ plow 12837 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12837) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610930562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365134562) : eMP 12837 0.011 xi bn ≤ 0.001175437844 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12837 : ℝ) * (1 - 0.011))) ≤ 0.000581209595 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365134562 / (12837 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581209595 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581209595 : ℝ) + 3.141593 * 0.052610930562 / (12837 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175437844 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610930562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365134562) : PiBarMP 12837 12 0.011 xi bn ≤ 0.160379599147 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12837 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036947727427 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.675609605628 : ℝ) ≤ √((12837 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.300485435853 : ℝ) ≤ √(12837 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12837) ≤ 0.122968654629 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036947727427 + 0.052610930562 * 1.772454 / (2 * (112.675609605628 : ℝ))) * (1 + 0.001175437844) +
        8 / (12837 * 113.300485435853) + 0.122968654629 := by gcongr
    _ ≤ (0.160379599147 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610930562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365134562) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281571196663) :
    parallelOracle 12837 0.011 xi bn cd ≤ 0.161359353609 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12837 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12837 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509697717 : ℝ) ≤ plow 12837 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.300485435853 : ℝ) ≤ √(12837 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281571196663 : ℝ) / (2 * 0.560509697717 * 113.300485435853)) * 0.160379599147 +
        0.281571196663 ^ 2 / (2 * 0.560509697717 * 113.300485435853) := by gcongr
    _ ≤ (0.161359353609 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610930562) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365134562)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281571196663) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12837 12837 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509697717 : ℝ) ≤ plow 12837 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.300485435853 : ℝ) ≤ √(12837 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12837 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12837 Θ 1.22 ≤ 0.011704279068 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.300485435853 := by gcongr <;> linarith
      _ ≤ (0.011704279068 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12837 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12837 12837 0.011 ≤ 0.008436742228 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12837 12837 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12837 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12837 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12837 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12837 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161359353609 + 0.011704279068 + (0.008436742228 : ℝ) *
        (1 + 2 * (0.281571196663 + 0.011704279068) / (0.560509697717 * 113.300485435853))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12837]

end BstLean.Part269.N12837

/-! The original eight local profiles supply actual 12837 moment certificates. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12837 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052610930562 ∧
    0 ≤ bN 12837 BstLean.Part154.csC (groupTheta g) ∧ bN 12837 BstLean.Part154.csC (groupTheta g) ≤ 0.001365134562 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12837 12837 0.011
      (momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12837 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12837 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12837 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229370727344 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12837 0.011
      (momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12837 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12837
/-! The actual computed-centre upper energy formula at 12837. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12837

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12837)
open BstLean.Part268 (cell12837)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085100445650
  | 2 => 0.086036248539
  | 3 => 0.086969212863
  | 4 => 0.087900528946
  | 5 => 0.088831643661
  | 6 => 0.089764299444
  | 7 => 0.090700577137
  | 8 => 0.091642942758
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12837 12837 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12837 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003397088065 + 0.003260455022 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S19.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S19.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12837

/-! Actual upper energy certificates on all 43 source endpoints at 12837. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12837)
open BstLean.Part268 (cell12837)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12837 (gMinus 12837) (1 - (cell12837 i).lower) ≤ 1 ∧
    energyUpper 12837 (gMinus 12837) (BstLean.Part211.gPlus 12837)
      (finiteEnergy 12837 12837 0.011) (1 - (cell12837 i).lower) ≤
      (cell12837 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨10,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨11,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨12,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨13,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨14,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨15,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨16,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨17,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨18,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨19,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨20,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨21,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨22,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨23,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨24,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨25,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨26,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨27,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨28,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨29,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨30,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨31,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨32,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨33,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨34,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨35,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨36,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨37,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨38,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨39,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨40,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨41,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨42,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨43,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨44,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨45,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨46,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨47,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨48,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨49,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨50,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨51,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12837) (by norm_num)
        (q := 1 - (cell12837 ⟨52,by decide⟩).lower)
        (by norm_num [cell12837]) (by norm_num [cell12837])
      exact ⟨E.1,E.2.trans (by norm_num [cell12837])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12837

/-! Source-cell containment and simple scalar guards at 12837. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12837)
open BstLean.Part268 (cell12837)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12837 ⟨10,by decide⟩).lower ∧ (cell12837 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12837 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12837 ⟨11,by decide⟩).lower ∧ (cell12837 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12837 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12837 ⟨12,by decide⟩).lower ∧ (cell12837 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12837 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12837 ⟨13,by decide⟩).lower ∧ (cell12837 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12837 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12837 ⟨14,by decide⟩).lower ∧ (cell12837 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12837 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12837 ⟨15,by decide⟩).lower ∧ (cell12837 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12837 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12837 ⟨16,by decide⟩).lower ∧ (cell12837 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12837 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12837 ⟨17,by decide⟩).lower ∧ (cell12837 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12837 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12837 ⟨18,by decide⟩).lower ∧ (cell12837 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12837 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12837 ⟨19,by decide⟩).lower ∧ (cell12837 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12837 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12837 ⟨20,by decide⟩).lower ∧ (cell12837 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12837 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12837 ⟨21,by decide⟩).lower ∧ (cell12837 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12837 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12837 ⟨22,by decide⟩).lower ∧ (cell12837 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12837 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12837 ⟨23,by decide⟩).lower ∧ (cell12837 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12837 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12837 ⟨24,by decide⟩).lower ∧ (cell12837 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12837 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12837 ⟨25,by decide⟩).lower ∧ (cell12837 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12837 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12837 ⟨26,by decide⟩).lower ∧ (cell12837 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12837 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12837 ⟨27,by decide⟩).lower ∧ (cell12837 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12837 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12837 ⟨28,by decide⟩).lower ∧ (cell12837 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12837 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12837 ⟨29,by decide⟩).lower ∧ (cell12837 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12837 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12837 ⟨30,by decide⟩).lower ∧ (cell12837 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12837 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12837 ⟨31,by decide⟩).lower ∧ (cell12837 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12837 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12837 ⟨32,by decide⟩).lower ∧ (cell12837 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12837 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12837 ⟨33,by decide⟩).lower ∧ (cell12837 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12837 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12837 ⟨34,by decide⟩).lower ∧ (cell12837 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12837 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12837 ⟨35,by decide⟩).lower ∧ (cell12837 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12837 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12837 ⟨36,by decide⟩).lower ∧ (cell12837 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12837 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12837 ⟨37,by decide⟩).lower ∧ (cell12837 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12837 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12837 ⟨38,by decide⟩).lower ∧ (cell12837 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12837 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12837 ⟨39,by decide⟩).lower ∧ (cell12837 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12837 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12837 ⟨40,by decide⟩).lower ∧ (cell12837 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12837 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12837 ⟨41,by decide⟩).lower ∧ (cell12837 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12837 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12837 ⟨42,by decide⟩).lower ∧ (cell12837 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12837 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12837 ⟨43,by decide⟩).lower ∧ (cell12837 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12837 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12837 ⟨44,by decide⟩).lower ∧ (cell12837 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12837 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12837 ⟨45,by decide⟩).lower ∧ (cell12837 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12837 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12837 ⟨46,by decide⟩).lower ∧ (cell12837 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12837 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12837 ⟨47,by decide⟩).lower ∧ (cell12837 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12837 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12837 ⟨48,by decide⟩).lower ∧ (cell12837 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12837 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12837 ⟨49,by decide⟩).lower ∧ (cell12837 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12837 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12837 ⟨50,by decide⟩).lower ∧ (cell12837 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12837 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12837 ⟨51,by decide⟩).lower ∧ (cell12837 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12837 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12837 ⟨52,by decide⟩).lower ∧ (cell12837 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12837 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12837 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12837 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12837,cell12837,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12837 i).lower ∧
    (cell12837 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12837 i).upper ≤ (0.532 : ℝ) ∧
    (cell12837 i).centre ≤ (0.1 : ℝ) ∧ (cell12837 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12837 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12837 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12837

/-! The local source numeric instances at 12837 have no network premises. -/
namespace BstLean.Part269.N12837
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12837)
open BstLean.Part268 (cell12837)

noncomputable def sourceNumerics12837 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12837 (cell12837 i)
      scalarRow12837.M scalarRow12837.H scalarRow12837.xi := by
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
    energy_allowance := scalarRow12837.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12837]
    centre_nonneg := (scalarRow12837.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12837])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12837