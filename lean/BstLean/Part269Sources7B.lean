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
import BstLean.Part269Direction7
import BstLean.Part269Shared7
import BstLean.Part269Finite
import BstLean.Part269Rows7
import BstLean.Part269Source
/-! Actual 12538 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12538 ≤ (1.036041860291 : ℝ) := by
  have hr : (111.973211081936 : ℝ) ≤ √(12538 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.973211081936 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12538 12538 (11 / 1000) ≤
    (0.008536747918 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12538) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.973211081936 : ℝ) ≤ √(12538 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12538)
  have hdiv : K / √(12538 : ℝ) ≤ K / 111.973211081936 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.973211081936 ≤ (0.008536747918 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12538.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12538 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12538 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12538 := gPlus_lower 12538
end BstLean.Part269.N12538

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12538
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036041860290 : ℝ) ≤ wn 12538 := by
  have hn : √(12538 : ℝ) ≤ 111.973211081937 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12538 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.973211081937 ≤ 2 / √(12538 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255192654 : ℝ) ≤ rhoBar 12538 BstLean.Part154.csC ∧
    rhoBar 12538 BstLean.Part154.csC ≤ 0.000255193049 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036041860290 : ℝ) / (1.295212 * 12538) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036041860291 : ℝ) / (1.29521 * 12538) := by gcongr
      _ ≤ (0.000255193049 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12538 BstLean.Part154.csC) ≤ 0.001020837320 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12538 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) ≤ 0.000194918292 ∧
    cc1 (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) ≤ 0.000124027779 ∧
    cc2 (rhoBar 12538 BstLean.Part154.csC) ≤ 0.000071999046 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12538 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12538 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12538 BstLean.Part154.csC * nuR (rhoBar 12538 BstLean.Part154.csC)) ≤ 0.000510402379 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255193049 : ℝ) * 0.001020837320 := by gcongr
      _ ≤ (0.000510402379 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12538 BstLean.Part154.csC) * nuR (rhoBar 12538 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020837320 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12538 BstLean.Part154.csC) * rhoBar 12538 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255193049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255193049 / 2 + 0.399 * 0.001020837320 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194918292 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510402379 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124027779 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255193049 / 1.414213562 := by gcongr
      _ ≤ (0.000071999046 : ℝ) := by norm_num

end BstLean.Part269.N12538

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12538
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) ≤ 1.64074E-7 := by
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12538 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12538 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12538 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194918292 : ℝ) ^ 2 + 0.000124027779 ^ 2 + 3 * 0.000071999046 ^ 2 +
        2 * 0.797885 * 0.000194918292 * 0.000124027779 + 2 * 0.000194918292 * 0.000071999046 +
        4 * 0.797885 * 0.000124027779 * 0.000071999046 := by gcongr
    _ ≤ (1.64074E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12538 BstLean.Part154.csC Θ ≤ 0.002664458080 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12538 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12538 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12538 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036041860291 * 1.64074E-7 / (0.000255192654 : ℝ) := by gcongr
    _ ≤ 0.002664458080 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12538 BstLean.Part154.csC Θ ≤ 0.002957026088 + 0.000673265482 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12538 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12538 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036041860291 : ℝ) * ((2 * Θ * 0.000255193049 +
        (6863 / 10000) * 0.000255193049 * 12538 * 0.001020837320) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002957026088 + 0.000673265482 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12538 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12538 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12538 0.011 Θ ∧ gammaRatio 12538 0.011 Θ ≤ 0.000087728771 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12538 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036041860291 : ℝ) * 0.525 / ((1 - 0.011) * 12538) := by gcongr
      _ ≤ (0.000087728771 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12538 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12538 0.011 Θ) :=
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
    badAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12538 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12538 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12538 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12538 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12538 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12538 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12538 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12538 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12538 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12538 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036041860291 : ℝ) * 12538 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003700068758 + 0.003337723562 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12538

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12538
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12538 BstLean.Part154.csC) (piBar (rhoBar 12538 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12538 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12538 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12538 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12538 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12538 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12538 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12538 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12538 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12538 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12538 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052825980616 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12538) ≤ 0.010665386565 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12538 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036041860291)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010665386565 + 2 * 0.737676 / 12538) := by gcongr
    _ ≤ (0.052825980616 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12538 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12538

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12538
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496147511 : ℝ) ≤ plow 12538 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12538) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958973629)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398840492) : eMP 12538 0.011 xi bn ≤ 0.001204047168 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12538 : ℝ) * (1 - 0.011))) ≤ 0.000595314937 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398840492 / (12538 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595314937 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595314937 : ℝ) + 3.141593 * 0.052958973629 / (12538 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204047168 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958973629)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398840492) : PiBarMP 12538 12 0.011 xi bn ≤ 0.162300053435 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12538 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037401076081 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.355655446860 : ℝ) ≤ √((12538 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.973211081936 : ℝ) ≤ √(12538 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12538) ≤ 0.124426263462 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037401076081 + 0.052958973629 * 1.772454 / (2 * (111.355655446860 : ℝ))) * (1 + 0.001204047168) +
        8 / (12538 * 111.973211081936) + 0.124426263462 := by gcongr
    _ ≤ (0.162300053435 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958973629)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398840492) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282954148447) :
    parallelOracle 12538 0.011 xi bn cd ≤ 0.163303761311 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12538 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12538 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496147511 : ℝ) ≤ plow 12538 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.973211081936 : ℝ) ≤ √(12538 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282954148447 : ℝ) / (2 * 0.560496147511 * 111.973211081936)) * 0.162300053435 +
        0.282954148447 ^ 2 / (2 * 0.560496147511 * 111.973211081936) := by gcongr
    _ ≤ (0.163303761311 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958973629) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398840492)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282954148447) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12538 12538 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496147511 : ℝ) ≤ plow 12538 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.973211081936 : ℝ) ≤ √(12538 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12538 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12538 Θ 1.22 ≤ 0.011843015729 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.973211081936 := by gcongr <;> linarith
      _ ≤ (0.011843015729 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12538 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12538 12538 0.011 ≤ 0.008536747918 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12538 12538 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12538 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12538 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12538 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12538 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163303761311 + 0.011843015729 + (0.008536747918 : ℝ) *
        (1 + 2 * (0.282954148447 + 0.011843015729) / (0.560496147511 * 111.973211081936))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12538]

end BstLean.Part269.N12538

/-! The original eight local profiles supply actual 12538 moment certificates. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12538 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052958973629 ∧
    0 ≤ bN 12538 BstLean.Part154.csC (groupTheta g) ∧ bN 12538 BstLean.Part154.csC (groupTheta g) ≤ 0.001398840492 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12538 12538 0.011
      (momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12538 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12538 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12538 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230128167831 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12538 0.011
      (momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12538 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12538
/-! The actual computed-centre upper energy formula at 12538. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12538

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12538)
open BstLean.Part268 (cell12538)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085977739888
  | 2 => 0.086929795918
  | 3 => 0.087881405006
  | 4 => 0.088834306614
  | 5 => 0.089790593375
  | 6 => 0.090752762051
  | 7 => 0.091723769013
  | 8 => 0.092707090245
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12538 12538 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12538 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12538

/-! Actual upper energy certificates on all 43 source endpoints at 12538. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12538)
open BstLean.Part268 (cell12538)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12538 (gMinus 12538) (1 - (cell12538 i).lower) ≤ 1 ∧
    energyUpper 12538 (gMinus 12538) (BstLean.Part211.gPlus 12538)
      (finiteEnergy 12538 12538 0.011) (1 - (cell12538 i).lower) ≤
      (cell12538 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨10,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨11,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨12,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨13,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨14,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨15,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨16,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨17,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨18,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨19,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨20,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨21,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨22,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨23,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨24,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨25,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨26,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨27,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨28,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨29,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨30,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨31,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨32,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨33,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨34,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨35,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨36,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨37,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨38,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨39,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨40,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨41,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨42,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨43,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨44,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨45,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨46,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨47,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨48,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨49,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨50,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨51,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12538) (by norm_num)
        (q := 1 - (cell12538 ⟨52,by decide⟩).lower)
        (by norm_num [cell12538]) (by norm_num [cell12538])
      exact ⟨E.1,E.2.trans (by norm_num [cell12538])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12538

/-! Source-cell containment and simple scalar guards at 12538. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12538)
open BstLean.Part268 (cell12538)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12538 ⟨10,by decide⟩).lower ∧ (cell12538 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12538 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12538 ⟨11,by decide⟩).lower ∧ (cell12538 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12538 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12538 ⟨12,by decide⟩).lower ∧ (cell12538 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12538 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12538 ⟨13,by decide⟩).lower ∧ (cell12538 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12538 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12538 ⟨14,by decide⟩).lower ∧ (cell12538 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12538 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12538 ⟨15,by decide⟩).lower ∧ (cell12538 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12538 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12538 ⟨16,by decide⟩).lower ∧ (cell12538 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12538 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12538 ⟨17,by decide⟩).lower ∧ (cell12538 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12538 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12538 ⟨18,by decide⟩).lower ∧ (cell12538 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12538 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12538 ⟨19,by decide⟩).lower ∧ (cell12538 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12538 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12538 ⟨20,by decide⟩).lower ∧ (cell12538 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12538 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12538 ⟨21,by decide⟩).lower ∧ (cell12538 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12538 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12538 ⟨22,by decide⟩).lower ∧ (cell12538 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12538 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12538 ⟨23,by decide⟩).lower ∧ (cell12538 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12538 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12538 ⟨24,by decide⟩).lower ∧ (cell12538 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12538 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12538 ⟨25,by decide⟩).lower ∧ (cell12538 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12538 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12538 ⟨26,by decide⟩).lower ∧ (cell12538 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12538 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12538 ⟨27,by decide⟩).lower ∧ (cell12538 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12538 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12538 ⟨28,by decide⟩).lower ∧ (cell12538 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12538 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12538 ⟨29,by decide⟩).lower ∧ (cell12538 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12538 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12538 ⟨30,by decide⟩).lower ∧ (cell12538 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12538 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12538 ⟨31,by decide⟩).lower ∧ (cell12538 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12538 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12538 ⟨32,by decide⟩).lower ∧ (cell12538 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12538 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12538 ⟨33,by decide⟩).lower ∧ (cell12538 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12538 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12538 ⟨34,by decide⟩).lower ∧ (cell12538 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12538 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12538 ⟨35,by decide⟩).lower ∧ (cell12538 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12538 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12538 ⟨36,by decide⟩).lower ∧ (cell12538 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12538 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12538 ⟨37,by decide⟩).lower ∧ (cell12538 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12538 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12538 ⟨38,by decide⟩).lower ∧ (cell12538 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12538 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12538 ⟨39,by decide⟩).lower ∧ (cell12538 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12538 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12538 ⟨40,by decide⟩).lower ∧ (cell12538 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12538 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12538 ⟨41,by decide⟩).lower ∧ (cell12538 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12538 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12538 ⟨42,by decide⟩).lower ∧ (cell12538 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12538 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12538 ⟨43,by decide⟩).lower ∧ (cell12538 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12538 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12538 ⟨44,by decide⟩).lower ∧ (cell12538 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12538 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12538 ⟨45,by decide⟩).lower ∧ (cell12538 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12538 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12538 ⟨46,by decide⟩).lower ∧ (cell12538 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12538 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12538 ⟨47,by decide⟩).lower ∧ (cell12538 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12538 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12538 ⟨48,by decide⟩).lower ∧ (cell12538 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12538 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12538 ⟨49,by decide⟩).lower ∧ (cell12538 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12538 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12538 ⟨50,by decide⟩).lower ∧ (cell12538 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12538 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12538 ⟨51,by decide⟩).lower ∧ (cell12538 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12538 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12538 ⟨52,by decide⟩).lower ∧ (cell12538 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12538 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12538 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12538 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12538,cell12538,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12538 i).lower ∧
    (cell12538 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12538 i).upper ≤ (0.532 : ℝ) ∧
    (cell12538 i).centre ≤ (0.1 : ℝ) ∧ (cell12538 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12538 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12538 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12538

/-! The local source numeric instances at 12538 have no network premises. -/
namespace BstLean.Part269.N12538
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12538)
open BstLean.Part268 (cell12538)

noncomputable def sourceNumerics12538 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12538 (cell12538 i)
      scalarRow12538.M scalarRow12538.H scalarRow12538.xi := by
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
    energy_allowance := scalarRow12538.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12538]
    centre_nonneg := (scalarRow12538.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12538])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12538
/-! Actual 12539 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12539 ≤ (1.036040410351 : ℝ) := by
  have hr : (111.977676346671 : ℝ) ≤ √(12539 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.977676346671 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12539 12539 (11 / 1000) ≤
    (0.008536407501 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12539) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.977676346671 : ℝ) ≤ √(12539 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12539)
  have hdiv : K / √(12539 : ℝ) ≤ K / 111.977676346671 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.977676346671 ≤ (0.008536407501 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12539.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12539 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12539 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12539 := gPlus_lower 12539
end BstLean.Part269.N12539

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12539
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036040410350 : ℝ) ≤ wn 12539 := by
  have hn : √(12539 : ℝ) ≤ 111.977676346672 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12539 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.977676346672 ≤ 2 / √(12539 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255171945 : ℝ) ≤ rhoBar 12539 BstLean.Part154.csC ∧
    rhoBar 12539 BstLean.Part154.csC ≤ 0.000255172340 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036040410350 : ℝ) / (1.295212 * 12539) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036040410351 : ℝ) / (1.29521 * 12539) := by gcongr
      _ ≤ (0.000255172340 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12539 BstLean.Part154.csC) ≤ 0.001020754473 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12539 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) ≤ 0.000194902473 ∧
    cc1 (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) ≤ 0.000124017713 ∧
    cc2 (rhoBar 12539 BstLean.Part154.csC) ≤ 0.000071993203 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12539 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12539 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12539 BstLean.Part154.csC * nuR (rhoBar 12539 BstLean.Part154.csC)) ≤ 0.000510360958 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255172340 : ℝ) * 0.001020754473 := by gcongr
      _ ≤ (0.000510360958 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12539 BstLean.Part154.csC) * nuR (rhoBar 12539 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020754473 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12539 BstLean.Part154.csC) * rhoBar 12539 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255172340 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255172340 / 2 + 0.399 * 0.001020754473 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194902473 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510360958 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124017713 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255172340 / 1.414213562 := by gcongr
      _ ≤ (0.000071993203 : ℝ) := by norm_num

end BstLean.Part269.N12539

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12539
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) ≤ 1.64048E-7 := by
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12539 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12539 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12539 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194902473 : ℝ) ^ 2 + 0.000124017713 ^ 2 + 3 * 0.000071993203 ^ 2 +
        2 * 0.797885 * 0.000194902473 * 0.000124017713 + 2 * 0.000194902473 * 0.000071993203 +
        4 * 0.797885 * 0.000124017713 * 0.000071993203 := by gcongr
    _ ≤ (1.64048E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12539 BstLean.Part154.csC Θ ≤ 0.002664248333 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12539 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12539 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12539 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036040410351 * 1.64048E-7 / (0.000255171945 : ℝ) := by gcongr
    _ ≤ 0.002664248333 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12539 BstLean.Part154.csC Θ ≤ 0.002956777832 + 0.000673209904 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12539 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12539 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036040410351 : ℝ) * ((2 * Θ * 0.000255172340 +
        (6863 / 10000) * 0.000255172340 * 12539 * 0.001020754473) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002956777832 + 0.000673209904 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12539 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12539 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12539 0.011 Θ ∧ gammaRatio 12539 0.011 Θ ≤ 0.000087721652 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12539 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036040410351 : ℝ) * 0.525 / ((1 - 0.011) * 12539) := by gcongr
      _ ≤ (0.000087721652 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12539 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12539 0.011 Θ) :=
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
    badAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12539 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12539 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12539 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12539 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12539 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12539 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12539 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12539 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12539 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12539 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036040410351 : ℝ) * 12539 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003699820502 + 0.003337458237 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12539

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12539
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12539 BstLean.Part154.csC) (piBar (rhoBar 12539 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12539 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12539 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12539 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12539 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12539 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12539 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12539 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12539 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12539 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12539 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052823851121 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12539) ≤ 0.010664961268 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12539 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036040410351)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010664961268 + 2 * 0.737676 / 12539) := by gcongr
    _ ≤ (0.052823851121 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12539 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12539

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12539
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496193907 : ℝ) ≤ plow 12539 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12539) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958586077)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398730375) : eMP 12539 0.011 xi bn ≤ 0.001203951660 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12539 : ℝ) * (1 - 0.011))) ≤ 0.000595267767 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398730375 / (12539 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595267767 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595267767 : ℝ) + 3.141593 * 0.052958586077 / (12539 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203951660 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958586077)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398730375) : PiBarMP 12539 12 0.011 xi bn ≤ 0.162293593646 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12539 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037399603942 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.360096084728 : ℝ) ≤ √((12539 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.977676346671 : ℝ) ≤ √(12539 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12539) ≤ 0.124421301793 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037399603942 + 0.052958586077 * 1.772454 / (2 * (111.360096084728 : ℝ))) * (1 + 0.001203951660) +
        8 / (12539 * 111.977676346671) + 0.124421301793 := by gcongr
    _ ≤ (0.162293593646 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958586077)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398730375) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282951176915) :
    parallelOracle 12539 0.011 xi bn cd ≤ 0.163297229615 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12539 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12539 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496193907 : ℝ) ≤ plow 12539 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.977676346671 : ℝ) ≤ √(12539 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282951176915 : ℝ) / (2 * 0.560496193907 * 111.977676346671)) * 0.162293593646 +
        0.282951176915 ^ 2 / (2 * 0.560496193907 * 111.977676346671) := by gcongr
    _ ≤ (0.163297229615 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958586077) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398730375)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282951176915) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12539 12539 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496193907 : ℝ) ≤ plow 12539 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.977676346671 : ℝ) ≤ √(12539 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12539 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12539 Θ 1.22 ≤ 0.011842543472 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.977676346671 := by gcongr <;> linarith
      _ ≤ (0.011842543472 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12539 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12539 12539 0.011 ≤ 0.008536407501 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12539 12539 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12539 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12539 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12539 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12539 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163297229615 + 0.011842543472 + (0.008536407501 : ℝ) *
        (1 + 2 * (0.282951176915 + 0.011842543472) / (0.560496193907 * 111.977676346671))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12539]

end BstLean.Part269.N12539

/-! The original eight local profiles supply actual 12539 moment certificates. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12539 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052958586077 ∧
    0 ≤ bN 12539 BstLean.Part154.csC (groupTheta g) ∧ bN 12539 BstLean.Part154.csC (groupTheta g) ≤ 0.001398730375 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12539 12539 0.011
      (momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12539 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12539 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12539 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230127325794 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12539 0.011
      (momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12539 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12539
/-! The actual computed-centre upper energy formula at 12539. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12539

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12539)
open BstLean.Part268 (cell12539)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085974633167
  | 2 => 0.086926627624
  | 3 => 0.087878165445
  | 4 => 0.088830983917
  | 5 => 0.089787173119
  | 6 => 0.090749226841
  | 7 => 0.091720098017
  | 8 => 0.092703258675
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12539 12539 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12539 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12539

/-! Actual upper energy certificates on all 43 source endpoints at 12539. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12539)
open BstLean.Part268 (cell12539)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12539 (gMinus 12539) (1 - (cell12539 i).lower) ≤ 1 ∧
    energyUpper 12539 (gMinus 12539) (BstLean.Part211.gPlus 12539)
      (finiteEnergy 12539 12539 0.011) (1 - (cell12539 i).lower) ≤
      (cell12539 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨10,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨11,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨12,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨13,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨14,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨15,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨16,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨17,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨18,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨19,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨20,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨21,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨22,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨23,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨24,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨25,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨26,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨27,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨28,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨29,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨30,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨31,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨32,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨33,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨34,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨35,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨36,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨37,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨38,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨39,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨40,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨41,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨42,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨43,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨44,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨45,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨46,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨47,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨48,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨49,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨50,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨51,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12539) (by norm_num)
        (q := 1 - (cell12539 ⟨52,by decide⟩).lower)
        (by norm_num [cell12539]) (by norm_num [cell12539])
      exact ⟨E.1,E.2.trans (by norm_num [cell12539])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12539

/-! Source-cell containment and simple scalar guards at 12539. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12539)
open BstLean.Part268 (cell12539)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12539 ⟨10,by decide⟩).lower ∧ (cell12539 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12539 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12539 ⟨11,by decide⟩).lower ∧ (cell12539 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12539 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12539 ⟨12,by decide⟩).lower ∧ (cell12539 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12539 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12539 ⟨13,by decide⟩).lower ∧ (cell12539 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12539 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12539 ⟨14,by decide⟩).lower ∧ (cell12539 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12539 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12539 ⟨15,by decide⟩).lower ∧ (cell12539 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12539 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12539 ⟨16,by decide⟩).lower ∧ (cell12539 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12539 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12539 ⟨17,by decide⟩).lower ∧ (cell12539 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12539 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12539 ⟨18,by decide⟩).lower ∧ (cell12539 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12539 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12539 ⟨19,by decide⟩).lower ∧ (cell12539 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12539 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12539 ⟨20,by decide⟩).lower ∧ (cell12539 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12539 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12539 ⟨21,by decide⟩).lower ∧ (cell12539 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12539 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12539 ⟨22,by decide⟩).lower ∧ (cell12539 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12539 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12539 ⟨23,by decide⟩).lower ∧ (cell12539 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12539 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12539 ⟨24,by decide⟩).lower ∧ (cell12539 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12539 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12539 ⟨25,by decide⟩).lower ∧ (cell12539 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12539 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12539 ⟨26,by decide⟩).lower ∧ (cell12539 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12539 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12539 ⟨27,by decide⟩).lower ∧ (cell12539 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12539 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12539 ⟨28,by decide⟩).lower ∧ (cell12539 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12539 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12539 ⟨29,by decide⟩).lower ∧ (cell12539 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12539 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12539 ⟨30,by decide⟩).lower ∧ (cell12539 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12539 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12539 ⟨31,by decide⟩).lower ∧ (cell12539 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12539 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12539 ⟨32,by decide⟩).lower ∧ (cell12539 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12539 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12539 ⟨33,by decide⟩).lower ∧ (cell12539 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12539 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12539 ⟨34,by decide⟩).lower ∧ (cell12539 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12539 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12539 ⟨35,by decide⟩).lower ∧ (cell12539 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12539 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12539 ⟨36,by decide⟩).lower ∧ (cell12539 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12539 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12539 ⟨37,by decide⟩).lower ∧ (cell12539 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12539 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12539 ⟨38,by decide⟩).lower ∧ (cell12539 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12539 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12539 ⟨39,by decide⟩).lower ∧ (cell12539 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12539 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12539 ⟨40,by decide⟩).lower ∧ (cell12539 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12539 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12539 ⟨41,by decide⟩).lower ∧ (cell12539 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12539 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12539 ⟨42,by decide⟩).lower ∧ (cell12539 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12539 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12539 ⟨43,by decide⟩).lower ∧ (cell12539 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12539 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12539 ⟨44,by decide⟩).lower ∧ (cell12539 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12539 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12539 ⟨45,by decide⟩).lower ∧ (cell12539 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12539 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12539 ⟨46,by decide⟩).lower ∧ (cell12539 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12539 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12539 ⟨47,by decide⟩).lower ∧ (cell12539 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12539 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12539 ⟨48,by decide⟩).lower ∧ (cell12539 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12539 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12539 ⟨49,by decide⟩).lower ∧ (cell12539 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12539 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12539 ⟨50,by decide⟩).lower ∧ (cell12539 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12539 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12539 ⟨51,by decide⟩).lower ∧ (cell12539 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12539 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12539 ⟨52,by decide⟩).lower ∧ (cell12539 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12539 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12539 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12539 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12539,cell12539,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12539 i).lower ∧
    (cell12539 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12539 i).upper ≤ (0.532 : ℝ) ∧
    (cell12539 i).centre ≤ (0.1 : ℝ) ∧ (cell12539 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12539 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12539 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12539

/-! The local source numeric instances at 12539 have no network premises. -/
namespace BstLean.Part269.N12539
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12539)
open BstLean.Part268 (cell12539)

noncomputable def sourceNumerics12539 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12539 (cell12539 i)
      scalarRow12539.M scalarRow12539.H scalarRow12539.xi := by
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
    energy_allowance := scalarRow12539.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12539]
    centre_nonneg := (scalarRow12539.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12539])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12539
/-! Actual 12540 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12540 ≤ (1.036038960585 : ℝ) := by
  have hr : (111.982141433355 : ℝ) ≤ √(12540 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.982141433355 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12540 12540 (11 / 1000) ≤
    (0.008536067124 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12540) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.982141433355 : ℝ) ≤ √(12540 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12540)
  have hdiv : K / √(12540 : ℝ) ≤ K / 111.982141433355 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.982141433355 ≤ (0.008536067124 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12540.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12540 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12540 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12540 := gPlus_lower 12540
end BstLean.Part269.N12540

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12540
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036038960584 : ℝ) ≤ wn 12540 := by
  have hn : √(12540 : ℝ) ≤ 111.982141433356 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12540 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.982141433356 ≤ 2 / √(12540 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255151239 : ℝ) ≤ rhoBar 12540 BstLean.Part154.csC ∧
    rhoBar 12540 BstLean.Part154.csC ≤ 0.000255151634 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036038960584 : ℝ) / (1.295212 * 12540) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036038960585 : ℝ) / (1.29521 * 12540) := by gcongr
      _ ≤ (0.000255151634 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12540 BstLean.Part154.csC) ≤ 0.001020671639 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12540 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) ≤ 0.000194886657 ∧
    cc1 (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) ≤ 0.000124007650 ∧
    cc2 (rhoBar 12540 BstLean.Part154.csC) ≤ 0.000071987361 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12540 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12540 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12540 BstLean.Part154.csC * nuR (rhoBar 12540 BstLean.Part154.csC)) ≤ 0.000510319544 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255151634 : ℝ) * 0.001020671639 := by gcongr
      _ ≤ (0.000510319544 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12540 BstLean.Part154.csC) * nuR (rhoBar 12540 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020671639 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12540 BstLean.Part154.csC) * rhoBar 12540 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255151634 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255151634 / 2 + 0.399 * 0.001020671639 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194886657 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510319544 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124007650 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255151634 / 1.414213562 := by gcongr
      _ ≤ (0.000071987361 : ℝ) := by norm_num

end BstLean.Part269.N12540

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12540
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) ≤ 1.64021E-7 := by
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12540 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12540 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12540 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194886657 : ℝ) ^ 2 + 0.000124007650 ^ 2 + 3 * 0.000071987361 ^ 2 +
        2 * 0.797885 * 0.000194886657 * 0.000124007650 + 2 * 0.000194886657 * 0.000071987361 +
        4 * 0.797885 * 0.000124007650 * 0.000071987361 := by gcongr
    _ ≤ (1.64021E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12540 BstLean.Part154.csC Θ ≤ 0.002664022280 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12540 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12540 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12540 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036038960585 * 1.64021E-7 / (0.000255151239 : ℝ) := by gcongr
    _ ≤ 0.002664022280 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12540 BstLean.Part154.csC Θ ≤ 0.002956529612 + 0.000673154334 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12540 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12540 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036038960585 : ℝ) * ((2 * Θ * 0.000255151634 +
        (6863 / 10000) * 0.000255151634 * 12540 * 0.001020671639) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002956529612 + 0.000673154334 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12540 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12540 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12540 0.011 Θ ∧ gammaRatio 12540 0.011 Θ ≤ 0.000087714534 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12540 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036038960585 : ℝ) * 0.525 / ((1 - 0.011) * 12540) := by gcongr
      _ ≤ (0.000087714534 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12540 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12540 0.011 Θ) :=
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
    badAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12540 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12540 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12540 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12540 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12540 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12540 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12540 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12540 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12540 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12540 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036038960585 : ℝ) * 12540 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003699572282 + 0.003337176614 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12540

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12540
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12540 BstLean.Part154.csC) (piBar (rhoBar 12540 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12540 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12540 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12540 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12540 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12540 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12540 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12540 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12540 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12540 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12540 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052821721883 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12540) ≤ 0.010664536022 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12540 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036038960585)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010664536022 + 2 * 0.737676 / 12540) := by gcongr
    _ ≤ (0.052821721883 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12540 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12540

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12540
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496240295 : ℝ) ≤ plow 12540 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12540) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958190005)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398611697) : eMP 12540 0.011 xi bn ≤ 0.001203852514 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12540 : ℝ) * (1 - 0.011))) ≤ 0.000595218779 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398611697 / (12540 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595218779 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595218779 : ℝ) + 3.141593 * 0.052958190005 / (12540 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203852514 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958190005)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398611697) : PiBarMP 12540 12 0.011 xi bn ≤ 0.162287019594 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12540 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037398017288 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.364536545526 : ℝ) ≤ √((12540 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.982141433355 : ℝ) ≤ √(12540 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12540) ≤ 0.124416340717 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037398017288 + 0.052958190005 * 1.772454 / (2 * (111.364536545526 : ℝ))) * (1 + 0.001203852514) +
        8 / (12540 * 111.982141433355) + 0.124416340717 := by gcongr
    _ ≤ (0.162287019594 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958190005)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398611697) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282948187126) :
    parallelOracle 12540 0.011 xi bn cd ≤ 0.163290583301 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12540 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12540 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496240295 : ℝ) ≤ plow 12540 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.982141433355 : ℝ) ≤ √(12540 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282948187126 : ℝ) / (2 * 0.560496240295 * 111.982141433355)) * 0.162287019594 +
        0.282948187126 ^ 2 / (2 * 0.560496240295 * 111.982141433355) := by gcongr
    _ ≤ (0.163290583301 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052958190005) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398611697)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282948187126) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12540 12540 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496240295 : ℝ) ≤ plow 12540 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.982141433355 : ℝ) ≤ √(12540 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12540 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12540 Θ 1.22 ≤ 0.011842071272 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.982141433355 := by gcongr <;> linarith
      _ ≤ (0.011842071272 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12540 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12540 12540 0.011 ≤ 0.008536067124 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12540 12540 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12540 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12540 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12540 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12540 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163290583301 + 0.011842071272 + (0.008536067124 : ℝ) *
        (1 + 2 * (0.282948187126 + 0.011842071272) / (0.560496240295 * 111.982141433355))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12540]

end BstLean.Part269.N12540

/-! The original eight local profiles supply actual 12540 moment certificates. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12540 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052958190005 ∧
    0 ≤ bN 12540 BstLean.Part154.csC (groupTheta g) ∧ bN 12540 BstLean.Part154.csC (groupTheta g) ≤ 0.001398611697 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12540 12540 0.011
      (momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12540 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12540 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12540 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230126465243 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12540 0.011
      (momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12540 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12540
/-! The actual computed-centre upper energy formula at 12540. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12540

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12540)
open BstLean.Part268 (cell12540)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085971527728
  | 2 => 0.086923460664
  | 3 => 0.087874927287
  | 4 => 0.088827662706
  | 5 => 0.089783754451
  | 6 => 0.090745693343
  | 7 => 0.091716428881
  | 8 => 0.092699429143
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12540 12540 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12540 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12540

/-! Actual upper energy certificates on all 43 source endpoints at 12540. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12540)
open BstLean.Part268 (cell12540)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12540 (gMinus 12540) (1 - (cell12540 i).lower) ≤ 1 ∧
    energyUpper 12540 (gMinus 12540) (BstLean.Part211.gPlus 12540)
      (finiteEnergy 12540 12540 0.011) (1 - (cell12540 i).lower) ≤
      (cell12540 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨10,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨11,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨12,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨13,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨14,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨15,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨16,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨17,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨18,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨19,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨20,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨21,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨22,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨23,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨24,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨25,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨26,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨27,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨28,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨29,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨30,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨31,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨32,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨33,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨34,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨35,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨36,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨37,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨38,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨39,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨40,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨41,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨42,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨43,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨44,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨45,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨46,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨47,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨48,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨49,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨50,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨51,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12540) (by norm_num)
        (q := 1 - (cell12540 ⟨52,by decide⟩).lower)
        (by norm_num [cell12540]) (by norm_num [cell12540])
      exact ⟨E.1,E.2.trans (by norm_num [cell12540])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12540

/-! Source-cell containment and simple scalar guards at 12540. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12540)
open BstLean.Part268 (cell12540)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12540 ⟨10,by decide⟩).lower ∧ (cell12540 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12540 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12540 ⟨11,by decide⟩).lower ∧ (cell12540 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12540 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12540 ⟨12,by decide⟩).lower ∧ (cell12540 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12540 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12540 ⟨13,by decide⟩).lower ∧ (cell12540 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12540 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12540 ⟨14,by decide⟩).lower ∧ (cell12540 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12540 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12540 ⟨15,by decide⟩).lower ∧ (cell12540 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12540 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12540 ⟨16,by decide⟩).lower ∧ (cell12540 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12540 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12540 ⟨17,by decide⟩).lower ∧ (cell12540 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12540 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12540 ⟨18,by decide⟩).lower ∧ (cell12540 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12540 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12540 ⟨19,by decide⟩).lower ∧ (cell12540 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12540 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12540 ⟨20,by decide⟩).lower ∧ (cell12540 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12540 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12540 ⟨21,by decide⟩).lower ∧ (cell12540 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12540 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12540 ⟨22,by decide⟩).lower ∧ (cell12540 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12540 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12540 ⟨23,by decide⟩).lower ∧ (cell12540 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12540 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12540 ⟨24,by decide⟩).lower ∧ (cell12540 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12540 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12540 ⟨25,by decide⟩).lower ∧ (cell12540 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12540 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12540 ⟨26,by decide⟩).lower ∧ (cell12540 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12540 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12540 ⟨27,by decide⟩).lower ∧ (cell12540 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12540 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12540 ⟨28,by decide⟩).lower ∧ (cell12540 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12540 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12540 ⟨29,by decide⟩).lower ∧ (cell12540 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12540 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12540 ⟨30,by decide⟩).lower ∧ (cell12540 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12540 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12540 ⟨31,by decide⟩).lower ∧ (cell12540 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12540 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12540 ⟨32,by decide⟩).lower ∧ (cell12540 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12540 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12540 ⟨33,by decide⟩).lower ∧ (cell12540 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12540 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12540 ⟨34,by decide⟩).lower ∧ (cell12540 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12540 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12540 ⟨35,by decide⟩).lower ∧ (cell12540 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12540 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12540 ⟨36,by decide⟩).lower ∧ (cell12540 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12540 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12540 ⟨37,by decide⟩).lower ∧ (cell12540 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12540 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12540 ⟨38,by decide⟩).lower ∧ (cell12540 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12540 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12540 ⟨39,by decide⟩).lower ∧ (cell12540 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12540 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12540 ⟨40,by decide⟩).lower ∧ (cell12540 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12540 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12540 ⟨41,by decide⟩).lower ∧ (cell12540 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12540 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12540 ⟨42,by decide⟩).lower ∧ (cell12540 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12540 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12540 ⟨43,by decide⟩).lower ∧ (cell12540 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12540 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12540 ⟨44,by decide⟩).lower ∧ (cell12540 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12540 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12540 ⟨45,by decide⟩).lower ∧ (cell12540 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12540 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12540 ⟨46,by decide⟩).lower ∧ (cell12540 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12540 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12540 ⟨47,by decide⟩).lower ∧ (cell12540 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12540 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12540 ⟨48,by decide⟩).lower ∧ (cell12540 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12540 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12540 ⟨49,by decide⟩).lower ∧ (cell12540 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12540 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12540 ⟨50,by decide⟩).lower ∧ (cell12540 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12540 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12540 ⟨51,by decide⟩).lower ∧ (cell12540 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12540 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12540 ⟨52,by decide⟩).lower ∧ (cell12540 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12540 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12540 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12540 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12540,cell12540,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12540 i).lower ∧
    (cell12540 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12540 i).upper ≤ (0.532 : ℝ) ∧
    (cell12540 i).centre ≤ (0.1 : ℝ) ∧ (cell12540 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12540 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12540 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12540

/-! The local source numeric instances at 12540 have no network premises. -/
namespace BstLean.Part269.N12540
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12540)
open BstLean.Part268 (cell12540)

noncomputable def sourceNumerics12540 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12540 (cell12540 i)
      scalarRow12540.M scalarRow12540.H scalarRow12540.xi := by
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
    energy_allowance := scalarRow12540.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12540]
    centre_nonneg := (scalarRow12540.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12540])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12540
/-! Actual 12541 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12541 ≤ (1.036037510994 : ℝ) := by
  have hr : (111.986606342008 : ℝ) ≤ √(12541 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.986606342008 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12541 12541 (11 / 1000) ≤
    (0.008535726789 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12541) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.986606342008 : ℝ) ≤ √(12541 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12541)
  have hdiv : K / √(12541 : ℝ) ≤ K / 111.986606342008 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.986606342008 ≤ (0.008535726789 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12541.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12541 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12541 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12541 := gPlus_lower 12541
end BstLean.Part269.N12541

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12541
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036037510993 : ℝ) ≤ wn 12541 := by
  have hn : √(12541 : ℝ) ≤ 111.986606342009 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12541 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.986606342009 ≤ 2 / √(12541 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255130537 : ℝ) ≤ rhoBar 12541 BstLean.Part154.csC ∧
    rhoBar 12541 BstLean.Part154.csC ≤ 0.000255130932 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036037510993 : ℝ) / (1.295212 * 12541) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036037510994 : ℝ) / (1.29521 * 12541) := by gcongr
      _ ≤ (0.000255130932 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12541 BstLean.Part154.csC) ≤ 0.001020588820 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12541 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) ≤ 0.000194870844 ∧
    cc1 (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) ≤ 0.000123997588 ∧
    cc2 (rhoBar 12541 BstLean.Part154.csC) ≤ 0.000071981521 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12541 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12541 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12541 BstLean.Part154.csC * nuR (rhoBar 12541 BstLean.Part154.csC)) ≤ 0.000510278137 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255130932 : ℝ) * 0.001020588820 := by gcongr
      _ ≤ (0.000510278137 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12541 BstLean.Part154.csC) * nuR (rhoBar 12541 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020588820 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12541 BstLean.Part154.csC) * rhoBar 12541 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255130932 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255130932 / 2 + 0.399 * 0.001020588820 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194870844 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510278137 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123997588 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255130932 / 1.414213562 := by gcongr
      _ ≤ (0.000071981521 : ℝ) := by norm_num

end BstLean.Part269.N12541

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12541
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) ≤ 1.63994E-7 := by
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12541 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12541 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12541 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194870844 : ℝ) ^ 2 + 0.000123997588 ^ 2 + 3 * 0.000071981521 ^ 2 +
        2 * 0.797885 * 0.000194870844 * 0.000123997588 + 2 * 0.000194870844 * 0.000071981521 +
        4 * 0.797885 * 0.000123997588 * 0.000071981521 := by gcongr
    _ ≤ (1.63994E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12541 BstLean.Part154.csC Θ ≤ 0.002663796151 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12541 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12541 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12541 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036037510994 * 1.63994E-7 / (0.000255130537 : ℝ) := by gcongr
    _ ≤ 0.002663796151 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12541 BstLean.Part154.csC Θ ≤ 0.002956281446 + 0.000673098775 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12541 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12541 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036037510994 : ℝ) * ((2 * Θ * 0.000255130932 +
        (6863 / 10000) * 0.000255130932 * 12541 * 0.001020588820) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002956281446 + 0.000673098775 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12541 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12541 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12541 0.011 Θ ∧ gammaRatio 12541 0.011 Θ ≤ 0.000087707417 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12541 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036037510994 : ℝ) * 0.525 / ((1 - 0.011) * 12541) := by gcongr
      _ ≤ (0.000087707417 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12541 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12541 0.011 Θ) :=
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
    badAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12541 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12541 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12541 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12541 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12541 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12541 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12541 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12541 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12541 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12541 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036037510994 : ℝ) * 12541 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003699324116 + 0.003336894926 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12541

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12541
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12541 BstLean.Part154.csC) (piBar (rhoBar 12541 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12541 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12541 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12541 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12541 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12541 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12541 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12541 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12541 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12541 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12541 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052819592897 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12541) ≤ 0.010664110826 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12541 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036037510994)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010664110826 + 2 * 0.737676 / 12541) := by gcongr
    _ ≤ (0.052819592897 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12541 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12541

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12541
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496286675 : ℝ) ≤ plow 12541 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12541) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957793953)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398492980) : eMP 12541 0.011 xi bn ≤ 0.001203753358 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12541 : ℝ) * (1 - 0.011))) ≤ 0.000595169786 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398492980 / (12541 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595169786 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595169786 : ℝ) + 3.141593 * 0.052957793953 / (12541 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203753358 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957793953)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398492980) : PiBarMP 12541 12 0.011 xi bn ≤ 0.162280445548 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12541 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037396430044 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.368976829276 : ℝ) ≤ √((12541 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.986606342008 : ℝ) ≤ √(12541 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12541) ≤ 0.124411380235 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037396430044 + 0.052957793953 * 1.772454 / (2 * (111.368976829276 : ℝ))) * (1 + 0.001203753358) +
        8 / (12541 * 111.986606342008) + 0.124411380235 := by gcongr
    _ ≤ (0.162280445548 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957793953)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398492980) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282945197629) :
    parallelOracle 12541 0.011 xi bn cd ≤ 0.163283937001 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12541 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12541 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496286675 : ℝ) ≤ plow 12541 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.986606342008 : ℝ) ≤ √(12541 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282945197629 : ℝ) / (2 * 0.560496286675 * 111.986606342008)) * 0.162280445548 +
        0.282945197629 ^ 2 / (2 * 0.560496286675 * 111.986606342008) := by gcongr
    _ ≤ (0.163283937001 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957793953) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398492980)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282945197629) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12541 12541 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496286675 : ℝ) ≤ plow 12541 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.986606342008 : ℝ) ≤ √(12541 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12541 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12541 Θ 1.22 ≤ 0.011841599128 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.986606342008 := by gcongr <;> linarith
      _ ≤ (0.011841599128 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12541 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12541 12541 0.011 ≤ 0.008535726789 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12541 12541 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12541 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12541 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12541 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12541 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163283937001 + 0.011841599128 + (0.008535726789 : ℝ) *
        (1 + 2 * (0.282945197629 + 0.011841599128) / (0.560496286675 * 111.986606342008))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12541]

end BstLean.Part269.N12541

/-! The original eight local profiles supply actual 12541 moment certificates. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12541 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052957793953 ∧
    0 ≤ bN 12541 BstLean.Part154.csC (groupTheta g) ∧ bN 12541 BstLean.Part154.csC (groupTheta g) ≤ 0.001398492980 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12541 12541 0.011
      (momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12541 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12541 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12541 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230125604732 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12541 0.011
      (momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12541 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12541
/-! The actual computed-centre upper energy formula at 12541. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12541

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12541)
open BstLean.Part268 (cell12541)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085968423567
  | 2 => 0.086920295039
  | 3 => 0.087871690530
  | 4 => 0.088824342979
  | 5 => 0.089780337368
  | 6 => 0.090742161554
  | 7 => 0.091712761602
  | 8 => 0.092695601646
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12541 12541 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12541 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12541

/-! Actual upper energy certificates on all 43 source endpoints at 12541. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12541)
open BstLean.Part268 (cell12541)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12541 (gMinus 12541) (1 - (cell12541 i).lower) ≤ 1 ∧
    energyUpper 12541 (gMinus 12541) (BstLean.Part211.gPlus 12541)
      (finiteEnergy 12541 12541 0.011) (1 - (cell12541 i).lower) ≤
      (cell12541 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨10,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨11,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨12,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨13,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨14,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨15,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨16,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨17,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨18,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨19,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨20,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨21,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨22,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨23,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨24,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨25,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨26,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨27,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨28,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨29,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨30,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨31,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨32,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨33,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨34,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨35,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨36,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨37,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨38,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨39,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨40,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨41,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨42,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨43,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨44,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨45,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨46,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨47,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨48,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨49,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨50,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨51,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12541) (by norm_num)
        (q := 1 - (cell12541 ⟨52,by decide⟩).lower)
        (by norm_num [cell12541]) (by norm_num [cell12541])
      exact ⟨E.1,E.2.trans (by norm_num [cell12541])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12541

/-! Source-cell containment and simple scalar guards at 12541. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12541)
open BstLean.Part268 (cell12541)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12541 ⟨10,by decide⟩).lower ∧ (cell12541 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12541 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12541 ⟨11,by decide⟩).lower ∧ (cell12541 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12541 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12541 ⟨12,by decide⟩).lower ∧ (cell12541 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12541 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12541 ⟨13,by decide⟩).lower ∧ (cell12541 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12541 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12541 ⟨14,by decide⟩).lower ∧ (cell12541 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12541 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12541 ⟨15,by decide⟩).lower ∧ (cell12541 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12541 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12541 ⟨16,by decide⟩).lower ∧ (cell12541 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12541 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12541 ⟨17,by decide⟩).lower ∧ (cell12541 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12541 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12541 ⟨18,by decide⟩).lower ∧ (cell12541 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12541 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12541 ⟨19,by decide⟩).lower ∧ (cell12541 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12541 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12541 ⟨20,by decide⟩).lower ∧ (cell12541 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12541 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12541 ⟨21,by decide⟩).lower ∧ (cell12541 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12541 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12541 ⟨22,by decide⟩).lower ∧ (cell12541 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12541 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12541 ⟨23,by decide⟩).lower ∧ (cell12541 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12541 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12541 ⟨24,by decide⟩).lower ∧ (cell12541 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12541 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12541 ⟨25,by decide⟩).lower ∧ (cell12541 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12541 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12541 ⟨26,by decide⟩).lower ∧ (cell12541 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12541 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12541 ⟨27,by decide⟩).lower ∧ (cell12541 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12541 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12541 ⟨28,by decide⟩).lower ∧ (cell12541 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12541 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12541 ⟨29,by decide⟩).lower ∧ (cell12541 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12541 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12541 ⟨30,by decide⟩).lower ∧ (cell12541 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12541 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12541 ⟨31,by decide⟩).lower ∧ (cell12541 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12541 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12541 ⟨32,by decide⟩).lower ∧ (cell12541 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12541 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12541 ⟨33,by decide⟩).lower ∧ (cell12541 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12541 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12541 ⟨34,by decide⟩).lower ∧ (cell12541 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12541 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12541 ⟨35,by decide⟩).lower ∧ (cell12541 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12541 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12541 ⟨36,by decide⟩).lower ∧ (cell12541 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12541 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12541 ⟨37,by decide⟩).lower ∧ (cell12541 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12541 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12541 ⟨38,by decide⟩).lower ∧ (cell12541 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12541 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12541 ⟨39,by decide⟩).lower ∧ (cell12541 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12541 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12541 ⟨40,by decide⟩).lower ∧ (cell12541 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12541 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12541 ⟨41,by decide⟩).lower ∧ (cell12541 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12541 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12541 ⟨42,by decide⟩).lower ∧ (cell12541 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12541 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12541 ⟨43,by decide⟩).lower ∧ (cell12541 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12541 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12541 ⟨44,by decide⟩).lower ∧ (cell12541 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12541 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12541 ⟨45,by decide⟩).lower ∧ (cell12541 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12541 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12541 ⟨46,by decide⟩).lower ∧ (cell12541 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12541 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12541 ⟨47,by decide⟩).lower ∧ (cell12541 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12541 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12541 ⟨48,by decide⟩).lower ∧ (cell12541 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12541 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12541 ⟨49,by decide⟩).lower ∧ (cell12541 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12541 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12541 ⟨50,by decide⟩).lower ∧ (cell12541 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12541 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12541 ⟨51,by decide⟩).lower ∧ (cell12541 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12541 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12541 ⟨52,by decide⟩).lower ∧ (cell12541 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12541 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12541 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12541 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12541,cell12541,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12541 i).lower ∧
    (cell12541 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12541 i).upper ≤ (0.532 : ℝ) ∧
    (cell12541 i).centre ≤ (0.1 : ℝ) ∧ (cell12541 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12541 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12541 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12541

/-! The local source numeric instances at 12541 have no network premises. -/
namespace BstLean.Part269.N12541
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12541)
open BstLean.Part268 (cell12541)

noncomputable def sourceNumerics12541 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12541 (cell12541 i)
      scalarRow12541.M scalarRow12541.H scalarRow12541.xi := by
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
    energy_allowance := scalarRow12541.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12541]
    centre_nonneg := (scalarRow12541.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12541])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12541
/-! Actual 12542 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12542 ≤ (1.036036061577 : ℝ) := by
  have hr : (111.991071072652 : ℝ) ≤ √(12542 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.991071072652 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12542 12542 (11 / 1000) ≤
    (0.008535386493 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12542) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.991071072652 : ℝ) ≤ √(12542 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12542)
  have hdiv : K / √(12542 : ℝ) ≤ K / 111.991071072652 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.991071072652 ≤ (0.008535386493 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12542.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12542 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12542 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12542 := gPlus_lower 12542
end BstLean.Part269.N12542

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12542
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036036061576 : ℝ) ≤ wn 12542 := by
  have hn : √(12542 : ℝ) ≤ 111.991071072653 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12542 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.991071072653 ≤ 2 / √(12542 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255109838 : ℝ) ≤ rhoBar 12542 BstLean.Part154.csC ∧
    rhoBar 12542 BstLean.Part154.csC ≤ 0.000255110233 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036036061576 : ℝ) / (1.295212 * 12542) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036036061577 : ℝ) / (1.29521 * 12542) := by gcongr
      _ ≤ (0.000255110233 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12542 BstLean.Part154.csC) ≤ 0.001020506014 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12542 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) ≤ 0.000194855033 ∧
    cc1 (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) ≤ 0.000123987528 ∧
    cc2 (rhoBar 12542 BstLean.Part154.csC) ≤ 0.000071975681 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12542 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12542 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12542 BstLean.Part154.csC * nuR (rhoBar 12542 BstLean.Part154.csC)) ≤ 0.000510236737 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255110233 : ℝ) * 0.001020506014 := by gcongr
      _ ≤ (0.000510236737 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12542 BstLean.Part154.csC) * nuR (rhoBar 12542 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020506014 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12542 BstLean.Part154.csC) * rhoBar 12542 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255110233 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255110233 / 2 + 0.399 * 0.001020506014 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194855033 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510236737 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123987528 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255110233 / 1.414213562 := by gcongr
      _ ≤ (0.000071975681 : ℝ) := by norm_num

end BstLean.Part269.N12542

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12542
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) ≤ 1.63968E-7 := by
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12542 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12542 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12542 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194855033 : ℝ) ^ 2 + 0.000123987528 ^ 2 + 3 * 0.000071975681 ^ 2 +
        2 * 0.797885 * 0.000194855033 * 0.000123987528 + 2 * 0.000194855033 * 0.000071975681 +
        4 * 0.797885 * 0.000123987528 * 0.000071975681 := by gcongr
    _ ≤ (1.63968E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12542 BstLean.Part154.csC Θ ≤ 0.002663586200 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12542 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12542 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12542 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036036061577 * 1.63968E-7 / (0.000255109838 : ℝ) := by gcongr
    _ ≤ 0.002663586200 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12542 BstLean.Part154.csC Θ ≤ 0.002956033316 + 0.000673043225 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12542 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12542 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036036061577 : ℝ) * ((2 * Θ * 0.000255110233 +
        (6863 / 10000) * 0.000255110233 * 12542 * 0.001020506014) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002956033316 + 0.000673043225 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12542 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12542 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12542 0.011 Θ ∧ gammaRatio 12542 0.011 Θ ≤ 0.000087700301 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12542 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036036061577 : ℝ) * 0.525 / ((1 - 0.011) * 12542) := by gcongr
      _ ≤ (0.000087700301 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12542 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12542 0.011 Θ) :=
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
    badAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12542 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12542 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12542 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12542 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12542 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12542 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12542 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12542 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12542 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12542 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036036061577 : ℝ) * 12542 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003699075986 + 0.003336629425 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12542

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12542
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12542 BstLean.Part154.csC) (piBar (rhoBar 12542 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12542 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12542 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12542 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12542 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12542 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12542 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12542 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12542 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12542 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12542 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052817464173 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12542) ≤ 0.010663685682 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12542 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036036061577)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010663685682 + 2 * 0.737676 / 12542) := by gcongr
    _ ≤ (0.052817464173 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12542 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12542

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12542
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496333048 : ℝ) ≤ plow 12542 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12542) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957406435)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398382755) : eMP 12542 0.011 xi bn ≤ 0.001203657828 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12542 : ℝ) * (1 - 0.011))) ≤ 0.000595122605 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398382755 / (12542 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595122605 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595122605 : ℝ) + 3.141593 * 0.052957406435 / (12542 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203657828 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957406435)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398382755) : PiBarMP 12542 12 0.011 xi bn ≤ 0.162273985917 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12542 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037394956278 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.373416935999 : ℝ) ≤ √((12542 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.991071072652 : ℝ) ≤ √(12542 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12542) ≤ 0.124406420346 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037394956278 + 0.052957406435 * 1.772454 / (2 * (111.373416935999 : ℝ))) * (1 + 0.001203657828) +
        8 / (12542 * 111.991071072652) + 0.124406420346 := by gcongr
    _ ≤ (0.162273985917 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957406435)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398382755) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282942226933) :
    parallelOracle 12542 0.011 xi bn cd ≤ 0.163277405492 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12542 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12542 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496333048 : ℝ) ≤ plow 12542 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.991071072652 : ℝ) ≤ √(12542 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282942226933 : ℝ) / (2 * 0.560496333048 * 111.991071072652)) * 0.162273985917 +
        0.282942226933 ^ 2 / (2 * 0.560496333048 * 111.991071072652) := by gcongr
    _ ≤ (0.163277405492 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957406435) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398382755)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282942226933) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12542 12542 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496333048 : ℝ) ≤ plow 12542 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.991071072652 : ℝ) ≤ √(12542 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12542 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12542 Θ 1.22 ≤ 0.011841127041 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.991071072652 := by gcongr <;> linarith
      _ ≤ (0.011841127041 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12542 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12542 12542 0.011 ≤ 0.008535386493 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12542 12542 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12542 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12542 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12542 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12542 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163277405492 + 0.011841127041 + (0.008535386493 : ℝ) *
        (1 + 2 * (0.282942226933 + 0.011841127041) / (0.560496333048 * 111.991071072652))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12542]

end BstLean.Part269.N12542

/-! The original eight local profiles supply actual 12542 moment certificates. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12542 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052957406435 ∧
    0 ≤ bN 12542 BstLean.Part154.csC (groupTheta g) ∧ bN 12542 BstLean.Part154.csC (groupTheta g) ≤ 0.001398382755 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12542 12542 0.011
      (momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12542 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12542 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12542 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230124762760 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12542 0.011
      (momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12542 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12542
/-! The actual computed-centre upper energy formula at 12542. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12542

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12542)
open BstLean.Part268 (cell12542)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085965320684
  | 2 => 0.086917130746
  | 3 => 0.087868455174
  | 4 => 0.088821024735
  | 5 => 0.089776921870
  | 6 => 0.090738631472
  | 7 => 0.091709096179
  | 8 => 0.092691776183
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12542 12542 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12542 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12542

/-! Actual upper energy certificates on all 43 source endpoints at 12542. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12542)
open BstLean.Part268 (cell12542)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12542 (gMinus 12542) (1 - (cell12542 i).lower) ≤ 1 ∧
    energyUpper 12542 (gMinus 12542) (BstLean.Part211.gPlus 12542)
      (finiteEnergy 12542 12542 0.011) (1 - (cell12542 i).lower) ≤
      (cell12542 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨10,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨11,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨12,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨13,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨14,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨15,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨16,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨17,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨18,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨19,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨20,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨21,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨22,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨23,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨24,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨25,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨26,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨27,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨28,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨29,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨30,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨31,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨32,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨33,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨34,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨35,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨36,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨37,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨38,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨39,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨40,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨41,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨42,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨43,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨44,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨45,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨46,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨47,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨48,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨49,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨50,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨51,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12542) (by norm_num)
        (q := 1 - (cell12542 ⟨52,by decide⟩).lower)
        (by norm_num [cell12542]) (by norm_num [cell12542])
      exact ⟨E.1,E.2.trans (by norm_num [cell12542])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12542

/-! Source-cell containment and simple scalar guards at 12542. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12542)
open BstLean.Part268 (cell12542)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12542 ⟨10,by decide⟩).lower ∧ (cell12542 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12542 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12542 ⟨11,by decide⟩).lower ∧ (cell12542 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12542 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12542 ⟨12,by decide⟩).lower ∧ (cell12542 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12542 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12542 ⟨13,by decide⟩).lower ∧ (cell12542 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12542 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12542 ⟨14,by decide⟩).lower ∧ (cell12542 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12542 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12542 ⟨15,by decide⟩).lower ∧ (cell12542 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12542 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12542 ⟨16,by decide⟩).lower ∧ (cell12542 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12542 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12542 ⟨17,by decide⟩).lower ∧ (cell12542 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12542 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12542 ⟨18,by decide⟩).lower ∧ (cell12542 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12542 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12542 ⟨19,by decide⟩).lower ∧ (cell12542 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12542 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12542 ⟨20,by decide⟩).lower ∧ (cell12542 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12542 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12542 ⟨21,by decide⟩).lower ∧ (cell12542 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12542 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12542 ⟨22,by decide⟩).lower ∧ (cell12542 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12542 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12542 ⟨23,by decide⟩).lower ∧ (cell12542 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12542 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12542 ⟨24,by decide⟩).lower ∧ (cell12542 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12542 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12542 ⟨25,by decide⟩).lower ∧ (cell12542 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12542 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12542 ⟨26,by decide⟩).lower ∧ (cell12542 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12542 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12542 ⟨27,by decide⟩).lower ∧ (cell12542 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12542 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12542 ⟨28,by decide⟩).lower ∧ (cell12542 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12542 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12542 ⟨29,by decide⟩).lower ∧ (cell12542 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12542 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12542 ⟨30,by decide⟩).lower ∧ (cell12542 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12542 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12542 ⟨31,by decide⟩).lower ∧ (cell12542 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12542 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12542 ⟨32,by decide⟩).lower ∧ (cell12542 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12542 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12542 ⟨33,by decide⟩).lower ∧ (cell12542 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12542 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12542 ⟨34,by decide⟩).lower ∧ (cell12542 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12542 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12542 ⟨35,by decide⟩).lower ∧ (cell12542 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12542 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12542 ⟨36,by decide⟩).lower ∧ (cell12542 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12542 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12542 ⟨37,by decide⟩).lower ∧ (cell12542 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12542 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12542 ⟨38,by decide⟩).lower ∧ (cell12542 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12542 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12542 ⟨39,by decide⟩).lower ∧ (cell12542 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12542 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12542 ⟨40,by decide⟩).lower ∧ (cell12542 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12542 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12542 ⟨41,by decide⟩).lower ∧ (cell12542 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12542 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12542 ⟨42,by decide⟩).lower ∧ (cell12542 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12542 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12542 ⟨43,by decide⟩).lower ∧ (cell12542 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12542 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12542 ⟨44,by decide⟩).lower ∧ (cell12542 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12542 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12542 ⟨45,by decide⟩).lower ∧ (cell12542 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12542 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12542 ⟨46,by decide⟩).lower ∧ (cell12542 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12542 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12542 ⟨47,by decide⟩).lower ∧ (cell12542 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12542 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12542 ⟨48,by decide⟩).lower ∧ (cell12542 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12542 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12542 ⟨49,by decide⟩).lower ∧ (cell12542 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12542 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12542 ⟨50,by decide⟩).lower ∧ (cell12542 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12542 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12542 ⟨51,by decide⟩).lower ∧ (cell12542 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12542 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12542 ⟨52,by decide⟩).lower ∧ (cell12542 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12542 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12542 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12542 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12542,cell12542,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12542 i).lower ∧
    (cell12542 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12542 i).upper ≤ (0.532 : ℝ) ∧
    (cell12542 i).centre ≤ (0.1 : ℝ) ∧ (cell12542 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12542 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12542 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12542

/-! The local source numeric instances at 12542 have no network premises. -/
namespace BstLean.Part269.N12542
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12542)
open BstLean.Part268 (cell12542)

noncomputable def sourceNumerics12542 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12542 (cell12542 i)
      scalarRow12542.M scalarRow12542.H scalarRow12542.xi := by
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
    energy_allowance := scalarRow12542.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12542]
    centre_nonneg := (scalarRow12542.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12542])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12542
/-! Actual 12543 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12543 ≤ (1.036034612334 : ℝ) := by
  have hr : (111.995535625309 : ℝ) ≤ √(12543 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.995535625309 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12543 12543 (11 / 1000) ≤
    (0.008535046239 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12543) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.995535625309 : ℝ) ≤ √(12543 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12543)
  have hdiv : K / √(12543 : ℝ) ≤ K / 111.995535625309 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.995535625309 ≤ (0.008535046239 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12543.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12543 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12543 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12543 := gPlus_lower 12543
end BstLean.Part269.N12543

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12543
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036034612333 : ℝ) ≤ wn 12543 := by
  have hn : √(12543 : ℝ) ≤ 111.995535625310 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12543 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.995535625310 ≤ 2 / √(12543 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255089142 : ℝ) ≤ rhoBar 12543 BstLean.Part154.csC ∧
    rhoBar 12543 BstLean.Part154.csC ≤ 0.000255089537 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036034612333 : ℝ) / (1.295212 * 12543) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036034612334 : ℝ) / (1.29521 * 12543) := by gcongr
      _ ≤ (0.000255089537 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12543 BstLean.Part154.csC) ≤ 0.001020423219 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12543 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) ≤ 0.000194839225 ∧
    cc1 (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) ≤ 0.000123977469 ∧
    cc2 (rhoBar 12543 BstLean.Part154.csC) ≤ 0.000071969842 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12543 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12543 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12543 BstLean.Part154.csC * nuR (rhoBar 12543 BstLean.Part154.csC)) ≤ 0.000510195342 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255089537 : ℝ) * 0.001020423219 := by gcongr
      _ ≤ (0.000510195342 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12543 BstLean.Part154.csC) * nuR (rhoBar 12543 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020423219 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12543 BstLean.Part154.csC) * rhoBar 12543 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255089537 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255089537 / 2 + 0.399 * 0.001020423219 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194839225 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510195342 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123977469 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255089537 / 1.414213562 := by gcongr
      _ ≤ (0.000071969842 : ℝ) := by norm_num

end BstLean.Part269.N12543

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12543
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) ≤ 1.63941E-7 := by
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12543 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12543 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12543 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194839225 : ℝ) ^ 2 + 0.000123977469 ^ 2 + 3 * 0.000071969842 ^ 2 +
        2 * 0.797885 * 0.000194839225 * 0.000123977469 + 2 * 0.000194839225 * 0.000071969842 +
        4 * 0.797885 * 0.000123977469 * 0.000071969842 := by gcongr
    _ ≤ (1.63941E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12543 BstLean.Part154.csC Θ ≤ 0.002663359939 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12543 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12543 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12543 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036034612334 * 1.63941E-7 / (0.000255089142 : ℝ) := by gcongr
    _ ≤ 0.002663359939 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12543 BstLean.Part154.csC Θ ≤ 0.002955785216 + 0.000672987682 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12543 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12543 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036034612334 : ℝ) * ((2 * Θ * 0.000255089537 +
        (6863 / 10000) * 0.000255089537 * 12543 * 0.001020423219) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002955785216 + 0.000672987682 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12543 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12543 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12543 0.011 Θ ∧ gammaRatio 12543 0.011 Θ ≤ 0.000087693187 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12543 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036034612334 : ℝ) * 0.525 / ((1 - 0.011) * 12543) := by gcongr
      _ ≤ (0.000087693187 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12543 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12543 0.011 Θ) :=
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
    badAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12543 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12543 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12543 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12543 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12543 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12543 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12543 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12543 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12543 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12543 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036034612334 : ℝ) * 12543 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003698827886 + 0.003336347621 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12543

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12543
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12543 BstLean.Part154.csC) (piBar (rhoBar 12543 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12543 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12543 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12543 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12543 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12543 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12543 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12543 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12543 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12543 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12543 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052815335702 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12543) ≤ 0.010663260588 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12543 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036034612334)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010663260588 + 2 * 0.737676 / 12543) := by gcongr
    _ ≤ (0.052815335702 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12543 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12543

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12543
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496379414 : ℝ) ≤ plow 12543 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12543) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957010388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398263968) : eMP 12543 0.011 xi bn ≤ 0.001203558658 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12543 : ℝ) * (1 - 0.011))) ≤ 0.000595073605 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398263968 / (12543 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595073605 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595073605 : ℝ) + 3.141593 * 0.052957010388 / (12543 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203558658 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957010388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398263968) : PiBarMP 12543 12 0.011 xi bn ≤ 0.162267411994 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12543 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037393367969 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.377856865716 : ℝ) ≤ √((12543 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.995535625309 : ℝ) ≤ √(12543 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12543) ≤ 0.124401461049 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037393367969 + 0.052957010388 * 1.772454 / (2 * (111.377856865716 : ℝ))) * (1 + 0.001203558658) +
        8 / (12543 * 111.995535625309) + 0.124401461049 := by gcongr
    _ ≤ (0.162267411994 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957010388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398263968) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282939237955) :
    parallelOracle 12543 0.011 xi bn cd ≤ 0.163270759335 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12543 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12543 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496379414 : ℝ) ≤ plow 12543 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.995535625309 : ℝ) ≤ √(12543 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282939237955 : ℝ) / (2 * 0.560496379414 * 111.995535625309)) * 0.162267411994 +
        0.282939237955 ^ 2 / (2 * 0.560496379414 * 111.995535625309) := by gcongr
    _ ≤ (0.163270759335 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052957010388) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398263968)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282939237955) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12543 12543 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496379414 : ℝ) ≤ plow 12543 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.995535625309 : ℝ) ≤ √(12543 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12543 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12543 Θ 1.22 ≤ 0.011840655011 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.995535625309 := by gcongr <;> linarith
      _ ≤ (0.011840655011 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12543 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12543 12543 0.011 ≤ 0.008535046239 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12543 12543 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12543 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12543 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12543 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12543 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163270759335 + 0.011840655011 + (0.008535046239 : ℝ) *
        (1 + 2 * (0.282939237955 + 0.011840655011) / (0.560496379414 * 111.995535625309))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12543]

end BstLean.Part269.N12543

/-! The original eight local profiles supply actual 12543 moment certificates. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12543 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052957010388 ∧
    0 ≤ bN 12543 BstLean.Part154.csC (groupTheta g) ∧ bN 12543 BstLean.Part154.csC (groupTheta g) ≤ 0.001398263968 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12543 12543 0.011
      (momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12543 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12543 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12543 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230123902253 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12543 0.011
      (momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12543 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12543
/-! The actual computed-centre upper energy formula at 12543. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12543

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12543)
open BstLean.Part268 (cell12543)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085962219078
  | 2 => 0.086913967784
  | 3 => 0.087865221216
  | 4 => 0.088817707973
  | 5 => 0.089773507954
  | 6 => 0.090735103094
  | 7 => 0.091705432608
  | 8 => 0.092687952750
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12543 12543 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12543 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12543

/-! Actual upper energy certificates on all 43 source endpoints at 12543. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12543)
open BstLean.Part268 (cell12543)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12543 (gMinus 12543) (1 - (cell12543 i).lower) ≤ 1 ∧
    energyUpper 12543 (gMinus 12543) (BstLean.Part211.gPlus 12543)
      (finiteEnergy 12543 12543 0.011) (1 - (cell12543 i).lower) ≤
      (cell12543 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨10,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨11,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨12,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨13,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨14,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨15,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨16,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨17,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨18,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨19,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨20,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨21,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨22,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨23,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨24,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨25,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨26,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨27,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨28,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨29,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨30,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨31,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨32,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨33,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨34,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨35,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨36,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨37,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨38,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨39,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨40,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨41,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨42,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨43,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨44,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨45,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨46,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨47,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨48,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨49,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨50,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨51,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12543) (by norm_num)
        (q := 1 - (cell12543 ⟨52,by decide⟩).lower)
        (by norm_num [cell12543]) (by norm_num [cell12543])
      exact ⟨E.1,E.2.trans (by norm_num [cell12543])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12543

/-! Source-cell containment and simple scalar guards at 12543. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12543)
open BstLean.Part268 (cell12543)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12543 ⟨10,by decide⟩).lower ∧ (cell12543 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12543 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12543 ⟨11,by decide⟩).lower ∧ (cell12543 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12543 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12543 ⟨12,by decide⟩).lower ∧ (cell12543 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12543 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12543 ⟨13,by decide⟩).lower ∧ (cell12543 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12543 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12543 ⟨14,by decide⟩).lower ∧ (cell12543 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12543 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12543 ⟨15,by decide⟩).lower ∧ (cell12543 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12543 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12543 ⟨16,by decide⟩).lower ∧ (cell12543 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12543 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12543 ⟨17,by decide⟩).lower ∧ (cell12543 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12543 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12543 ⟨18,by decide⟩).lower ∧ (cell12543 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12543 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12543 ⟨19,by decide⟩).lower ∧ (cell12543 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12543 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12543 ⟨20,by decide⟩).lower ∧ (cell12543 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12543 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12543 ⟨21,by decide⟩).lower ∧ (cell12543 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12543 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12543 ⟨22,by decide⟩).lower ∧ (cell12543 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12543 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12543 ⟨23,by decide⟩).lower ∧ (cell12543 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12543 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12543 ⟨24,by decide⟩).lower ∧ (cell12543 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12543 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12543 ⟨25,by decide⟩).lower ∧ (cell12543 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12543 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12543 ⟨26,by decide⟩).lower ∧ (cell12543 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12543 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12543 ⟨27,by decide⟩).lower ∧ (cell12543 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12543 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12543 ⟨28,by decide⟩).lower ∧ (cell12543 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12543 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12543 ⟨29,by decide⟩).lower ∧ (cell12543 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12543 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12543 ⟨30,by decide⟩).lower ∧ (cell12543 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12543 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12543 ⟨31,by decide⟩).lower ∧ (cell12543 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12543 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12543 ⟨32,by decide⟩).lower ∧ (cell12543 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12543 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12543 ⟨33,by decide⟩).lower ∧ (cell12543 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12543 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12543 ⟨34,by decide⟩).lower ∧ (cell12543 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12543 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12543 ⟨35,by decide⟩).lower ∧ (cell12543 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12543 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12543 ⟨36,by decide⟩).lower ∧ (cell12543 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12543 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12543 ⟨37,by decide⟩).lower ∧ (cell12543 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12543 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12543 ⟨38,by decide⟩).lower ∧ (cell12543 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12543 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12543 ⟨39,by decide⟩).lower ∧ (cell12543 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12543 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12543 ⟨40,by decide⟩).lower ∧ (cell12543 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12543 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12543 ⟨41,by decide⟩).lower ∧ (cell12543 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12543 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12543 ⟨42,by decide⟩).lower ∧ (cell12543 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12543 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12543 ⟨43,by decide⟩).lower ∧ (cell12543 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12543 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12543 ⟨44,by decide⟩).lower ∧ (cell12543 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12543 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12543 ⟨45,by decide⟩).lower ∧ (cell12543 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12543 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12543 ⟨46,by decide⟩).lower ∧ (cell12543 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12543 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12543 ⟨47,by decide⟩).lower ∧ (cell12543 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12543 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12543 ⟨48,by decide⟩).lower ∧ (cell12543 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12543 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12543 ⟨49,by decide⟩).lower ∧ (cell12543 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12543 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12543 ⟨50,by decide⟩).lower ∧ (cell12543 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12543 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12543 ⟨51,by decide⟩).lower ∧ (cell12543 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12543 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12543 ⟨52,by decide⟩).lower ∧ (cell12543 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12543 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12543 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12543 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12543,cell12543,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12543 i).lower ∧
    (cell12543 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12543 i).upper ≤ (0.532 : ℝ) ∧
    (cell12543 i).centre ≤ (0.1 : ℝ) ∧ (cell12543 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12543 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12543 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12543

/-! The local source numeric instances at 12543 have no network premises. -/
namespace BstLean.Part269.N12543
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12543)
open BstLean.Part268 (cell12543)

noncomputable def sourceNumerics12543 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12543 (cell12543 i)
      scalarRow12543.M scalarRow12543.H scalarRow12543.xi := by
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
    energy_allowance := scalarRow12543.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12543]
    centre_nonneg := (scalarRow12543.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12543])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12543
/-! Actual 12544 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12544 ≤ (1.036033163266 : ℝ) := by
  have hr : (112.000000000000 : ℝ) ≤ √(12544 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.000000000000 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12544 12544 (11 / 1000) ≤
    (0.008534706025 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12544) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.000000000000 : ℝ) ≤ √(12544 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12544)
  have hdiv : K / √(12544 : ℝ) ≤ K / 112.000000000000 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.000000000000 ≤ (0.008534706025 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12544.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12544 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12544 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12544 := gPlus_lower 12544
end BstLean.Part269.N12544

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12544
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036033163265 : ℝ) ≤ wn 12544 := by
  have hn : √(12544 : ℝ) ≤ 112.000000000000 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12544 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.000000000000 ≤ 2 / √(12544 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255068450 : ℝ) ≤ rhoBar 12544 BstLean.Part154.csC ∧
    rhoBar 12544 BstLean.Part154.csC ≤ 0.000255068845 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036033163265 : ℝ) / (1.295212 * 12544) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036033163266 : ℝ) / (1.29521 * 12544) := by gcongr
      _ ≤ (0.000255068845 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12544 BstLean.Part154.csC) ≤ 0.001020340441 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12544 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) ≤ 0.000194823419 ∧
    cc1 (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) ≤ 0.000123967412 ∧
    cc2 (rhoBar 12544 BstLean.Part154.csC) ≤ 0.000071964004 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12544 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12544 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12544 BstLean.Part154.csC * nuR (rhoBar 12544 BstLean.Part154.csC)) ≤ 0.000510153955 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255068845 : ℝ) * 0.001020340441 := by gcongr
      _ ≤ (0.000510153955 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12544 BstLean.Part154.csC) * nuR (rhoBar 12544 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020340441 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12544 BstLean.Part154.csC) * rhoBar 12544 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255068845 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255068845 / 2 + 0.399 * 0.001020340441 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194823419 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510153955 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123967412 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255068845 / 1.414213562 := by gcongr
      _ ≤ (0.000071964004 : ℝ) := by norm_num

end BstLean.Part269.N12544

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12544
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) ≤ 1.63915E-7 := by
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12544 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12544 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12544 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194823419 : ℝ) ^ 2 + 0.000123967412 ^ 2 + 3 * 0.000071964004 ^ 2 +
        2 * 0.797885 * 0.000194823419 * 0.000123967412 + 2 * 0.000194823419 * 0.000071964004 +
        4 * 0.797885 * 0.000123967412 * 0.000071964004 := by gcongr
    _ ≤ (1.63915E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12544 BstLean.Part154.csC Θ ≤ 0.002663149848 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12544 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12544 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12544 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036033163266 * 1.63915E-7 / (0.000255068450 : ℝ) := by gcongr
    _ ≤ 0.002663149848 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12544 BstLean.Part154.csC Θ ≤ 0.002955537176 + 0.000672932150 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12544 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12544 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036033163266 : ℝ) * ((2 * Θ * 0.000255068845 +
        (6863 / 10000) * 0.000255068845 * 12544 * 0.001020340441) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002955537176 + 0.000672932150 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12544 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12544 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12544 0.011 Θ ∧ gammaRatio 12544 0.011 Θ ≤ 0.000087686073 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12544 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036033163266 : ℝ) * 0.525 / ((1 - 0.011) * 12544) := by gcongr
      _ ≤ (0.000087686073 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12544 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12544 0.011 Θ) :=
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
    badAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12544 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12544 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12544 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12544 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12544 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12544 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12544 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12544 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12544 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12544 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036033163266 : ℝ) * 12544 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003698579846 + 0.003336081998 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12544

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12544
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12544 BstLean.Part154.csC) (piBar (rhoBar 12544 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12544 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12544 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12544 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12544 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12544 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12544 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12544 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12544 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12544 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12544 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052813207492 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12544) ≤ 0.010662835546 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12544 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036033163266)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010662835546 + 2 * 0.737676 / 12544) := by gcongr
    _ ≤ (0.052813207492 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12544 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12544

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12544
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496425773 : ℝ) ≤ plow 12544 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12544) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956622895)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398153671) : eMP 12544 0.011 xi bn ≤ 0.001203463111 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12544 : ℝ) * (1 - 0.011))) ≤ 0.000595026415 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398153671 / (12544 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595026415 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595026415 : ℝ) + 3.141593 * 0.052956622895 / (12544 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203463111 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956622895)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398153671) : PiBarMP 12544 12 0.011 xi bn ≤ 0.162260952469 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12544 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037391893119 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.382296618448 : ℝ) ≤ √((12544 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.000000000000 : ℝ) ≤ √(12544 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12544) ≤ 0.124396502346 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037391893119 + 0.052956622895 * 1.772454 / (2 * (111.382296618448 : ℝ))) * (1 + 0.001203463111) +
        8 / (12544 * 112.000000000000) + 0.124396502346 := by gcongr
    _ ≤ (0.162260952469 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956622895)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398153671) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282936267821) :
    parallelOracle 12544 0.011 xi bn cd ≤ 0.163264227951 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12544 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12544 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496425773 : ℝ) ≤ plow 12544 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.000000000000 : ℝ) ≤ √(12544 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282936267821 : ℝ) / (2 * 0.560496425773 * 112.000000000000)) * 0.162260952469 +
        0.282936267821 ^ 2 / (2 * 0.560496425773 * 112.000000000000) := by gcongr
    _ ≤ (0.163264227951 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956622895) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398153671)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282936267821) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12544 12544 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496425773 : ℝ) ≤ plow 12544 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.000000000000 : ℝ) ≤ √(12544 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12544 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12544 Θ 1.22 ≤ 0.011840183036 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.000000000000 := by gcongr <;> linarith
      _ ≤ (0.011840183036 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12544 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12544 12544 0.011 ≤ 0.008534706025 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12544 12544 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12544 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12544 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12544 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12544 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163264227951 + 0.011840183036 + (0.008534706025 : ℝ) *
        (1 + 2 * (0.282936267821 + 0.011840183036) / (0.560496425773 * 112.000000000000))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12544]

end BstLean.Part269.N12544

/-! The original eight local profiles supply actual 12544 moment certificates. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12544 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052956622895 ∧
    0 ≤ bN 12544 BstLean.Part154.csC (groupTheta g) ∧ bN 12544 BstLean.Part154.csC (groupTheta g) ≤ 0.001398153671 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12544 12544 0.011
      (momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12544 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12544 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12544 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230123060329 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12544 0.011
      (momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12544 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12544
/-! The actual computed-centre upper energy formula at 12544. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12544

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12544)
open BstLean.Part268 (cell12544)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085959118747
  | 2 => 0.086910806152
  | 3 => 0.087861988655
  | 4 => 0.088814392690
  | 5 => 0.089770095619
  | 6 => 0.090731576420
  | 7 => 0.091701770889
  | 8 => 0.092684131346
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12544 12544 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12544 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12544

/-! Actual upper energy certificates on all 43 source endpoints at 12544. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12544)
open BstLean.Part268 (cell12544)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12544 (gMinus 12544) (1 - (cell12544 i).lower) ≤ 1 ∧
    energyUpper 12544 (gMinus 12544) (BstLean.Part211.gPlus 12544)
      (finiteEnergy 12544 12544 0.011) (1 - (cell12544 i).lower) ≤
      (cell12544 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨10,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨11,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨12,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨13,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨14,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨15,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨16,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨17,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨18,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨19,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨20,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨21,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨22,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨23,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨24,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨25,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨26,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨27,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨28,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨29,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨30,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨31,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨32,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨33,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨34,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨35,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨36,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨37,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨38,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨39,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨40,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨41,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨42,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨43,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨44,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨45,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨46,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨47,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨48,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨49,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨50,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨51,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12544) (by norm_num)
        (q := 1 - (cell12544 ⟨52,by decide⟩).lower)
        (by norm_num [cell12544]) (by norm_num [cell12544])
      exact ⟨E.1,E.2.trans (by norm_num [cell12544])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12544

/-! Source-cell containment and simple scalar guards at 12544. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12544)
open BstLean.Part268 (cell12544)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12544 ⟨10,by decide⟩).lower ∧ (cell12544 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12544 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12544 ⟨11,by decide⟩).lower ∧ (cell12544 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12544 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12544 ⟨12,by decide⟩).lower ∧ (cell12544 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12544 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12544 ⟨13,by decide⟩).lower ∧ (cell12544 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12544 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12544 ⟨14,by decide⟩).lower ∧ (cell12544 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12544 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12544 ⟨15,by decide⟩).lower ∧ (cell12544 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12544 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12544 ⟨16,by decide⟩).lower ∧ (cell12544 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12544 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12544 ⟨17,by decide⟩).lower ∧ (cell12544 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12544 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12544 ⟨18,by decide⟩).lower ∧ (cell12544 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12544 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12544 ⟨19,by decide⟩).lower ∧ (cell12544 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12544 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12544 ⟨20,by decide⟩).lower ∧ (cell12544 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12544 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12544 ⟨21,by decide⟩).lower ∧ (cell12544 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12544 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12544 ⟨22,by decide⟩).lower ∧ (cell12544 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12544 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12544 ⟨23,by decide⟩).lower ∧ (cell12544 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12544 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12544 ⟨24,by decide⟩).lower ∧ (cell12544 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12544 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12544 ⟨25,by decide⟩).lower ∧ (cell12544 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12544 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12544 ⟨26,by decide⟩).lower ∧ (cell12544 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12544 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12544 ⟨27,by decide⟩).lower ∧ (cell12544 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12544 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12544 ⟨28,by decide⟩).lower ∧ (cell12544 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12544 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12544 ⟨29,by decide⟩).lower ∧ (cell12544 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12544 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12544 ⟨30,by decide⟩).lower ∧ (cell12544 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12544 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12544 ⟨31,by decide⟩).lower ∧ (cell12544 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12544 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12544 ⟨32,by decide⟩).lower ∧ (cell12544 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12544 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12544 ⟨33,by decide⟩).lower ∧ (cell12544 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12544 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12544 ⟨34,by decide⟩).lower ∧ (cell12544 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12544 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12544 ⟨35,by decide⟩).lower ∧ (cell12544 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12544 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12544 ⟨36,by decide⟩).lower ∧ (cell12544 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12544 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12544 ⟨37,by decide⟩).lower ∧ (cell12544 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12544 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12544 ⟨38,by decide⟩).lower ∧ (cell12544 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12544 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12544 ⟨39,by decide⟩).lower ∧ (cell12544 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12544 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12544 ⟨40,by decide⟩).lower ∧ (cell12544 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12544 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12544 ⟨41,by decide⟩).lower ∧ (cell12544 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12544 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12544 ⟨42,by decide⟩).lower ∧ (cell12544 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12544 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12544 ⟨43,by decide⟩).lower ∧ (cell12544 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12544 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12544 ⟨44,by decide⟩).lower ∧ (cell12544 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12544 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12544 ⟨45,by decide⟩).lower ∧ (cell12544 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12544 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12544 ⟨46,by decide⟩).lower ∧ (cell12544 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12544 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12544 ⟨47,by decide⟩).lower ∧ (cell12544 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12544 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12544 ⟨48,by decide⟩).lower ∧ (cell12544 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12544 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12544 ⟨49,by decide⟩).lower ∧ (cell12544 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12544 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12544 ⟨50,by decide⟩).lower ∧ (cell12544 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12544 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12544 ⟨51,by decide⟩).lower ∧ (cell12544 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12544 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12544 ⟨52,by decide⟩).lower ∧ (cell12544 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12544 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12544 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12544 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12544,cell12544,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12544 i).lower ∧
    (cell12544 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12544 i).upper ≤ (0.532 : ℝ) ∧
    (cell12544 i).centre ≤ (0.1 : ℝ) ∧ (cell12544 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12544 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12544 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12544

/-! The local source numeric instances at 12544 have no network premises. -/
namespace BstLean.Part269.N12544
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12544)
open BstLean.Part268 (cell12544)

noncomputable def sourceNumerics12544 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12544 (cell12544 i)
      scalarRow12544.M scalarRow12544.H scalarRow12544.xi := by
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
    energy_allowance := scalarRow12544.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12544]
    centre_nonneg := (scalarRow12544.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12544])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12544
/-! Actual 12545 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12545 ≤ (1.036031714372 : ℝ) := by
  have hr : (112.004464196745 : ℝ) ≤ √(12545 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.004464196745 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12545 12545 (11 / 1000) ≤
    (0.008534365852 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12545) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.004464196745 : ℝ) ≤ √(12545 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12545)
  have hdiv : K / √(12545 : ℝ) ≤ K / 112.004464196745 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.004464196745 ≤ (0.008534365852 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12545.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12545 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12545 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12545 := gPlus_lower 12545
end BstLean.Part269.N12545

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12545
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036031714371 : ℝ) ≤ wn 12545 := by
  have hn : √(12545 : ℝ) ≤ 112.004464196746 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12545 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.004464196746 ≤ 2 / √(12545 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255047761 : ℝ) ≤ rhoBar 12545 BstLean.Part154.csC ∧
    rhoBar 12545 BstLean.Part154.csC ≤ 0.000255048156 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036031714371 : ℝ) / (1.295212 * 12545) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036031714372 : ℝ) / (1.29521 * 12545) := by gcongr
      _ ≤ (0.000255048156 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12545 BstLean.Part154.csC) ≤ 0.001020257674 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12545 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) ≤ 0.000194807616 ∧
    cc1 (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) ≤ 0.000123957356 ∧
    cc2 (rhoBar 12545 BstLean.Part154.csC) ≤ 0.000071958166 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12545 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12545 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12545 BstLean.Part154.csC * nuR (rhoBar 12545 BstLean.Part154.csC)) ≤ 0.000510112575 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255048156 : ℝ) * 0.001020257674 := by gcongr
      _ ≤ (0.000510112575 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12545 BstLean.Part154.csC) * nuR (rhoBar 12545 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020257674 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12545 BstLean.Part154.csC) * rhoBar 12545 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255048156 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255048156 / 2 + 0.399 * 0.001020257674 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194807616 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510112575 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123957356 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255048156 / 1.414213562 := by gcongr
      _ ≤ (0.000071958166 : ℝ) := by norm_num

end BstLean.Part269.N12545

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12545
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) ≤ 1.63888E-7 := by
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12545 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12545 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12545 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194807616 : ℝ) ^ 2 + 0.000123957356 ^ 2 + 3 * 0.000071958166 ^ 2 +
        2 * 0.797885 * 0.000194807616 * 0.000123957356 + 2 * 0.000194807616 * 0.000071958166 +
        4 * 0.797885 * 0.000123957356 * 0.000071958166 := by gcongr
    _ ≤ (1.63888E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12545 BstLean.Part154.csC Θ ≤ 0.002662923446 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12545 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12545 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12545 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036031714372 * 1.63888E-7 / (0.000255047761 : ℝ) := by gcongr
    _ ≤ 0.002662923446 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12545 BstLean.Part154.csC Θ ≤ 0.002955289165 + 0.000672876627 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12545 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12545 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036031714372 : ℝ) * ((2 * Θ * 0.000255048156 +
        (6863 / 10000) * 0.000255048156 * 12545 * 0.001020257674) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002955289165 + 0.000672876627 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12545 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12545 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12545 0.011 Θ ∧ gammaRatio 12545 0.011 Θ ≤ 0.000087678961 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12545 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036031714372 : ℝ) * 0.525 / ((1 - 0.011) * 12545) := by gcongr
      _ ≤ (0.000087678961 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12545 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12545 0.011 Θ) :=
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
    badAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12545 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12545 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12545 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12545 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12545 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12545 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12545 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12545 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12545 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12545 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036031714372 : ℝ) * 12545 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003698331835 + 0.003335800073 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12545

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12545
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12545 BstLean.Part154.csC) (piBar (rhoBar 12545 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12545 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12545 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12545 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12545 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12545 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12545 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12545 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12545 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12545 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12545 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052811079535 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12545) ≤ 0.010662410554 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12545 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036031714372)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010662410554 + 2 * 0.737676 / 12545) := by gcongr
    _ ≤ (0.052811079535 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12545 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12545

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12545
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496472124 : ℝ) ≤ plow 12545 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12545) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956226874)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398034810) : eMP 12545 0.011 xi bn ≤ 0.001203363926 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12545 : ℝ) * (1 - 0.011))) ≤ 0.000594977407 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398034810 / (12545 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594977407 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594977407 : ℝ) + 3.141593 * 0.052956226874 / (12545 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203363926 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956226874)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398034810) : PiBarMP 12545 12 0.011 xi bn ≤ 0.162254378617 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12545 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037390303690 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.386736194216 : ℝ) ≤ √((12545 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.004464196745 : ℝ) ≤ √(12545 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12545) ≤ 0.124391544236 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037390303690 + 0.052956226874 * 1.772454 / (2 * (111.386736194216 : ℝ))) * (1 + 0.001203363926) +
        8 / (12545 * 112.004464196745) + 0.124391544236 := by gcongr
    _ ≤ (0.162254378617 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956226874)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398034810) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282933279408) :
    parallelOracle 12545 0.011 xi bn cd ≤ 0.163257581883 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12545 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12545 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496472124 : ℝ) ≤ plow 12545 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.004464196745 : ℝ) ≤ √(12545 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282933279408 : ℝ) / (2 * 0.560496472124 * 112.004464196745)) * 0.162254378617 +
        0.282933279408 ^ 2 / (2 * 0.560496472124 * 112.004464196745) := by gcongr
    _ ≤ (0.163257581883 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052956226874) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398034810)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282933279408) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12545 12545 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496472124 : ℝ) ≤ plow 12545 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.004464196745 : ℝ) ≤ √(12545 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12545 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12545 Θ 1.22 ≤ 0.011839711118 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.004464196745 := by gcongr <;> linarith
      _ ≤ (0.011839711118 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12545 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12545 12545 0.011 ≤ 0.008534365852 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12545 12545 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12545 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12545 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12545 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12545 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163257581883 + 0.011839711118 + (0.008534365852 : ℝ) *
        (1 + 2 * (0.282933279408 + 0.011839711118) / (0.560496472124 * 112.004464196745))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12545]

end BstLean.Part269.N12545

/-! The original eight local profiles supply actual 12545 moment certificates. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12545 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052956226874 ∧
    0 ≤ bN 12545 BstLean.Part154.csC (groupTheta g) ∧ bN 12545 BstLean.Part154.csC (groupTheta g) ≤ 0.001398034810 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12545 12545 0.011
      (momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12545 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12545 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12545 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230122199873 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12545 0.011
      (momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12545 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12545
/-! The actual computed-centre upper energy formula at 12545. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12545

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12545)
open BstLean.Part268 (cell12545)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085956019689
  | 2 => 0.086907645848
  | 3 => 0.087858757490
  | 4 => 0.088811078886
  | 5 => 0.089766684863
  | 6 => 0.090728051447
  | 7 => 0.091698111019
  | 8 => 0.092680311968
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12545 12545 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12545 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12545

/-! Actual upper energy certificates on all 43 source endpoints at 12545. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12545)
open BstLean.Part268 (cell12545)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12545 (gMinus 12545) (1 - (cell12545 i).lower) ≤ 1 ∧
    energyUpper 12545 (gMinus 12545) (BstLean.Part211.gPlus 12545)
      (finiteEnergy 12545 12545 0.011) (1 - (cell12545 i).lower) ≤
      (cell12545 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨10,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨11,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨12,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨13,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨14,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨15,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨16,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨17,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨18,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨19,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨20,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨21,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨22,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨23,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨24,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨25,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨26,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨27,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨28,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨29,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨30,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨31,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨32,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨33,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨34,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨35,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨36,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨37,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨38,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨39,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨40,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨41,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨42,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨43,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨44,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨45,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨46,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨47,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨48,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨49,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨50,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨51,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12545) (by norm_num)
        (q := 1 - (cell12545 ⟨52,by decide⟩).lower)
        (by norm_num [cell12545]) (by norm_num [cell12545])
      exact ⟨E.1,E.2.trans (by norm_num [cell12545])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12545

/-! Source-cell containment and simple scalar guards at 12545. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12545)
open BstLean.Part268 (cell12545)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12545 ⟨10,by decide⟩).lower ∧ (cell12545 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12545 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12545 ⟨11,by decide⟩).lower ∧ (cell12545 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12545 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12545 ⟨12,by decide⟩).lower ∧ (cell12545 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12545 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12545 ⟨13,by decide⟩).lower ∧ (cell12545 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12545 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12545 ⟨14,by decide⟩).lower ∧ (cell12545 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12545 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12545 ⟨15,by decide⟩).lower ∧ (cell12545 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12545 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12545 ⟨16,by decide⟩).lower ∧ (cell12545 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12545 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12545 ⟨17,by decide⟩).lower ∧ (cell12545 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12545 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12545 ⟨18,by decide⟩).lower ∧ (cell12545 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12545 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12545 ⟨19,by decide⟩).lower ∧ (cell12545 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12545 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12545 ⟨20,by decide⟩).lower ∧ (cell12545 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12545 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12545 ⟨21,by decide⟩).lower ∧ (cell12545 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12545 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12545 ⟨22,by decide⟩).lower ∧ (cell12545 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12545 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12545 ⟨23,by decide⟩).lower ∧ (cell12545 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12545 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12545 ⟨24,by decide⟩).lower ∧ (cell12545 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12545 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12545 ⟨25,by decide⟩).lower ∧ (cell12545 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12545 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12545 ⟨26,by decide⟩).lower ∧ (cell12545 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12545 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12545 ⟨27,by decide⟩).lower ∧ (cell12545 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12545 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12545 ⟨28,by decide⟩).lower ∧ (cell12545 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12545 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12545 ⟨29,by decide⟩).lower ∧ (cell12545 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12545 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12545 ⟨30,by decide⟩).lower ∧ (cell12545 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12545 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12545 ⟨31,by decide⟩).lower ∧ (cell12545 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12545 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12545 ⟨32,by decide⟩).lower ∧ (cell12545 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12545 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12545 ⟨33,by decide⟩).lower ∧ (cell12545 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12545 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12545 ⟨34,by decide⟩).lower ∧ (cell12545 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12545 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12545 ⟨35,by decide⟩).lower ∧ (cell12545 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12545 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12545 ⟨36,by decide⟩).lower ∧ (cell12545 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12545 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12545 ⟨37,by decide⟩).lower ∧ (cell12545 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12545 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12545 ⟨38,by decide⟩).lower ∧ (cell12545 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12545 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12545 ⟨39,by decide⟩).lower ∧ (cell12545 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12545 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12545 ⟨40,by decide⟩).lower ∧ (cell12545 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12545 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12545 ⟨41,by decide⟩).lower ∧ (cell12545 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12545 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12545 ⟨42,by decide⟩).lower ∧ (cell12545 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12545 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12545 ⟨43,by decide⟩).lower ∧ (cell12545 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12545 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12545 ⟨44,by decide⟩).lower ∧ (cell12545 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12545 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12545 ⟨45,by decide⟩).lower ∧ (cell12545 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12545 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12545 ⟨46,by decide⟩).lower ∧ (cell12545 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12545 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12545 ⟨47,by decide⟩).lower ∧ (cell12545 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12545 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12545 ⟨48,by decide⟩).lower ∧ (cell12545 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12545 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12545 ⟨49,by decide⟩).lower ∧ (cell12545 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12545 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12545 ⟨50,by decide⟩).lower ∧ (cell12545 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12545 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12545 ⟨51,by decide⟩).lower ∧ (cell12545 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12545 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12545 ⟨52,by decide⟩).lower ∧ (cell12545 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12545 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12545 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12545 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12545,cell12545,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12545 i).lower ∧
    (cell12545 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12545 i).upper ≤ (0.532 : ℝ) ∧
    (cell12545 i).centre ≤ (0.1 : ℝ) ∧ (cell12545 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12545 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12545 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12545

/-! The local source numeric instances at 12545 have no network premises. -/
namespace BstLean.Part269.N12545
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12545)
open BstLean.Part268 (cell12545)

noncomputable def sourceNumerics12545 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12545 (cell12545 i)
      scalarRow12545.M scalarRow12545.H scalarRow12545.xi := by
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
    energy_allowance := scalarRow12545.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12545]
    centre_nonneg := (scalarRow12545.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12545])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12545
/-! Actual 12546 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12546 ≤ (1.036030265652 : ℝ) := by
  have hr : (112.008928215566 : ℝ) ≤ √(12546 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.008928215566 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12546 12546 (11 / 1000) ≤
    (0.008534025720 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12546) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.008928215566 : ℝ) ≤ √(12546 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12546)
  have hdiv : K / √(12546 : ℝ) ≤ K / 112.008928215566 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.008928215566 ≤ (0.008534025720 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12546.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12546 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12546 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12546 := gPlus_lower 12546
end BstLean.Part269.N12546

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12546
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036030265651 : ℝ) ≤ wn 12546 := by
  have hn : √(12546 : ℝ) ≤ 112.008928215567 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12546 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.008928215567 ≤ 2 / √(12546 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255027075 : ℝ) ≤ rhoBar 12546 BstLean.Part154.csC ∧
    rhoBar 12546 BstLean.Part154.csC ≤ 0.000255027470 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036030265651 : ℝ) / (1.295212 * 12546) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036030265652 : ℝ) / (1.29521 * 12546) := by gcongr
      _ ≤ (0.000255027470 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12546 BstLean.Part154.csC) ≤ 0.001020174920 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12546 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) ≤ 0.000194791815 ∧
    cc1 (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) ≤ 0.000123947302 ∧
    cc2 (rhoBar 12546 BstLean.Part154.csC) ≤ 0.000071952330 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12546 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12546 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12546 BstLean.Part154.csC * nuR (rhoBar 12546 BstLean.Part154.csC)) ≤ 0.000510071200 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255027470 : ℝ) * 0.001020174920 := by gcongr
      _ ≤ (0.000510071200 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12546 BstLean.Part154.csC) * nuR (rhoBar 12546 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020174920 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12546 BstLean.Part154.csC) * rhoBar 12546 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255027470 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255027470 / 2 + 0.399 * 0.001020174920 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194791815 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510071200 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123947302 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255027470 / 1.414213562 := by gcongr
      _ ≤ (0.000071952330 : ℝ) := by norm_num

end BstLean.Part269.N12546

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12546
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) ≤ 1.63861E-7 := by
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12546 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12546 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12546 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194791815 : ℝ) ^ 2 + 0.000123947302 ^ 2 + 3 * 0.000071952330 ^ 2 +
        2 * 0.797885 * 0.000194791815 * 0.000123947302 + 2 * 0.000194791815 * 0.000071952330 +
        4 * 0.797885 * 0.000123947302 * 0.000071952330 := by gcongr
    _ ≤ (1.63861E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12546 BstLean.Part154.csC Θ ≤ 0.002662696977 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12546 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12546 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12546 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036030265652 * 1.63861E-7 / (0.000255027075 : ℝ) := by gcongr
    _ ≤ 0.002662696977 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12546 BstLean.Part154.csC Θ ≤ 0.002955041191 + 0.000672821112 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12546 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12546 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036030265652 : ℝ) * ((2 * Θ * 0.000255027470 +
        (6863 / 10000) * 0.000255027470 * 12546 * 0.001020174920) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002955041191 + 0.000672821112 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12546 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12546 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12546 0.011 Θ ∧ gammaRatio 12546 0.011 Θ ≤ 0.000087671850 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12546 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036030265652 : ℝ) * 0.525 / ((1 - 0.011) * 12546) := by gcongr
      _ ≤ (0.000087671850 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12546 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12546 0.011 Θ) :=
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
    badAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12546 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12546 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12546 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12546 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12546 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12546 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12546 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12546 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12546 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12546 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036030265652 : ℝ) * 12546 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003698083861 + 0.003335518089 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12546

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12546
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12546 BstLean.Part154.csC) (piBar (rhoBar 12546 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12546 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12546 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12546 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12546 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12546 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12546 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12546 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12546 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12546 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12546 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052808951835 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12546) ≤ 0.010661985613 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12546 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036030265652)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010661985613 + 2 * 0.737676 / 12546) := by gcongr
    _ ≤ (0.052808951835 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12546 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12546

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12546
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496518468 : ℝ) ≤ plow 12546 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12546) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955830858)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397915913) : eMP 12546 0.011 xi bn ≤ 0.001203264733 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12546 : ℝ) * (1 - 0.011))) ≤ 0.000594928395 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397915913 / (12546 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594928395 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594928395 : ℝ) + 3.141593 * 0.052955830858 / (12546 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203264733 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955830858)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397915913) : PiBarMP 12546 12 0.011 xi bn ≤ 0.162247804810 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12546 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037388713712 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.391175593042 : ℝ) ≤ √((12546 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.008928215566 : ℝ) ≤ √(12546 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12546) ≤ 0.124386586719 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037388713712 + 0.052955830858 * 1.772454 / (2 * (111.391175593042 : ℝ))) * (1 + 0.001203264733) +
        8 / (12546 * 112.008928215566) + 0.124386586719 := by gcongr
    _ ≤ (0.162247804810 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955830858)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397915913) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282930291259) :
    parallelOracle 12546 0.011 xi bn cd ≤ 0.163250935871 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12546 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12546 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496518468 : ℝ) ≤ plow 12546 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.008928215566 : ℝ) ≤ √(12546 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282930291259 : ℝ) / (2 * 0.560496518468 * 112.008928215566)) * 0.162247804810 +
        0.282930291259 ^ 2 / (2 * 0.560496518468 * 112.008928215566) := by gcongr
    _ ≤ (0.163250935871 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955830858) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397915913)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282930291259) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12546 12546 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496518468 : ℝ) ≤ plow 12546 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.008928215566 : ℝ) ≤ √(12546 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12546 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12546 Θ 1.22 ≤ 0.011839239257 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.008928215566 := by gcongr <;> linarith
      _ ≤ (0.011839239257 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12546 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12546 12546 0.011 ≤ 0.008534025720 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12546 12546 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12546 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12546 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12546 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12546 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163250935871 + 0.011839239257 + (0.008534025720 : ℝ) *
        (1 + 2 * (0.282930291259 + 0.011839239257) / (0.560496518468 * 112.008928215566))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12546]

end BstLean.Part269.N12546

/-! The original eight local profiles supply actual 12546 moment certificates. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12546 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052955830858 ∧
    0 ≤ bN 12546 BstLean.Part154.csC (groupTheta g) ∧ bN 12546 BstLean.Part154.csC (groupTheta g) ≤ 0.001397915913 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12546 12546 0.011
      (momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12546 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12546 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12546 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230121339424 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12546 0.011
      (momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12546 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12546
/-! The actual computed-centre upper energy formula at 12546. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12546

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12546)
open BstLean.Part268 (cell12546)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085952921904
  | 2 => 0.086904486871
  | 3 => 0.087855527718
  | 4 => 0.088807766558
  | 5 => 0.089763275684
  | 6 => 0.090724528174
  | 7 => 0.091694452995
  | 8 => 0.092676494614
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12546 12546 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12546 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12546

/-! Actual upper energy certificates on all 43 source endpoints at 12546. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12546)
open BstLean.Part268 (cell12546)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12546 (gMinus 12546) (1 - (cell12546 i).lower) ≤ 1 ∧
    energyUpper 12546 (gMinus 12546) (BstLean.Part211.gPlus 12546)
      (finiteEnergy 12546 12546 0.011) (1 - (cell12546 i).lower) ≤
      (cell12546 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨10,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨11,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨12,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨13,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨14,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨15,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨16,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨17,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨18,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨19,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨20,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨21,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨22,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨23,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨24,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨25,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨26,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨27,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨28,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨29,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨30,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨31,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨32,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨33,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨34,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨35,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨36,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨37,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨38,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨39,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨40,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨41,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨42,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨43,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨44,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨45,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨46,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨47,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨48,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨49,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨50,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨51,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12546) (by norm_num)
        (q := 1 - (cell12546 ⟨52,by decide⟩).lower)
        (by norm_num [cell12546]) (by norm_num [cell12546])
      exact ⟨E.1,E.2.trans (by norm_num [cell12546])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12546

/-! Source-cell containment and simple scalar guards at 12546. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12546)
open BstLean.Part268 (cell12546)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12546 ⟨10,by decide⟩).lower ∧ (cell12546 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12546 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12546 ⟨11,by decide⟩).lower ∧ (cell12546 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12546 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12546 ⟨12,by decide⟩).lower ∧ (cell12546 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12546 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12546 ⟨13,by decide⟩).lower ∧ (cell12546 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12546 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12546 ⟨14,by decide⟩).lower ∧ (cell12546 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12546 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12546 ⟨15,by decide⟩).lower ∧ (cell12546 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12546 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12546 ⟨16,by decide⟩).lower ∧ (cell12546 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12546 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12546 ⟨17,by decide⟩).lower ∧ (cell12546 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12546 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12546 ⟨18,by decide⟩).lower ∧ (cell12546 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12546 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12546 ⟨19,by decide⟩).lower ∧ (cell12546 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12546 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12546 ⟨20,by decide⟩).lower ∧ (cell12546 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12546 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12546 ⟨21,by decide⟩).lower ∧ (cell12546 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12546 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12546 ⟨22,by decide⟩).lower ∧ (cell12546 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12546 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12546 ⟨23,by decide⟩).lower ∧ (cell12546 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12546 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12546 ⟨24,by decide⟩).lower ∧ (cell12546 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12546 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12546 ⟨25,by decide⟩).lower ∧ (cell12546 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12546 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12546 ⟨26,by decide⟩).lower ∧ (cell12546 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12546 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12546 ⟨27,by decide⟩).lower ∧ (cell12546 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12546 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12546 ⟨28,by decide⟩).lower ∧ (cell12546 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12546 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12546 ⟨29,by decide⟩).lower ∧ (cell12546 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12546 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12546 ⟨30,by decide⟩).lower ∧ (cell12546 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12546 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12546 ⟨31,by decide⟩).lower ∧ (cell12546 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12546 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12546 ⟨32,by decide⟩).lower ∧ (cell12546 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12546 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12546 ⟨33,by decide⟩).lower ∧ (cell12546 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12546 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12546 ⟨34,by decide⟩).lower ∧ (cell12546 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12546 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12546 ⟨35,by decide⟩).lower ∧ (cell12546 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12546 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12546 ⟨36,by decide⟩).lower ∧ (cell12546 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12546 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12546 ⟨37,by decide⟩).lower ∧ (cell12546 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12546 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12546 ⟨38,by decide⟩).lower ∧ (cell12546 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12546 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12546 ⟨39,by decide⟩).lower ∧ (cell12546 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12546 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12546 ⟨40,by decide⟩).lower ∧ (cell12546 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12546 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12546 ⟨41,by decide⟩).lower ∧ (cell12546 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12546 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12546 ⟨42,by decide⟩).lower ∧ (cell12546 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12546 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12546 ⟨43,by decide⟩).lower ∧ (cell12546 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12546 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12546 ⟨44,by decide⟩).lower ∧ (cell12546 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12546 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12546 ⟨45,by decide⟩).lower ∧ (cell12546 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12546 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12546 ⟨46,by decide⟩).lower ∧ (cell12546 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12546 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12546 ⟨47,by decide⟩).lower ∧ (cell12546 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12546 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12546 ⟨48,by decide⟩).lower ∧ (cell12546 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12546 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12546 ⟨49,by decide⟩).lower ∧ (cell12546 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12546 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12546 ⟨50,by decide⟩).lower ∧ (cell12546 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12546 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12546 ⟨51,by decide⟩).lower ∧ (cell12546 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12546 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12546 ⟨52,by decide⟩).lower ∧ (cell12546 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12546 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12546 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12546 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12546,cell12546,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12546 i).lower ∧
    (cell12546 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12546 i).upper ≤ (0.532 : ℝ) ∧
    (cell12546 i).centre ≤ (0.1 : ℝ) ∧ (cell12546 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12546 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12546 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12546

/-! The local source numeric instances at 12546 have no network premises. -/
namespace BstLean.Part269.N12546
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12546)
open BstLean.Part268 (cell12546)

noncomputable def sourceNumerics12546 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12546 (cell12546 i)
      scalarRow12546.M scalarRow12546.H scalarRow12546.xi := by
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
    energy_allowance := scalarRow12546.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12546]
    centre_nonneg := (scalarRow12546.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12546])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12546
/-! Actual 12547 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12547 ≤ (1.036028817106 : ℝ) := by
  have hr : (112.013392056485 : ℝ) ≤ √(12547 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.013392056485 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12547 12547 (11 / 1000) ≤
    (0.008533685628 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12547) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.013392056485 : ℝ) ≤ √(12547 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12547)
  have hdiv : K / √(12547 : ℝ) ≤ K / 112.013392056485 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.013392056485 ≤ (0.008533685628 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12547.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12547 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12547 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12547 := gPlus_lower 12547
end BstLean.Part269.N12547

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12547
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036028817105 : ℝ) ≤ wn 12547 := by
  have hn : √(12547 : ℝ) ≤ 112.013392056486 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12547 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.013392056486 ≤ 2 / √(12547 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255006393 : ℝ) ≤ rhoBar 12547 BstLean.Part154.csC ∧
    rhoBar 12547 BstLean.Part154.csC ≤ 0.000255006788 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036028817105 : ℝ) / (1.295212 * 12547) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036028817106 : ℝ) / (1.29521 * 12547) := by gcongr
      _ ≤ (0.000255006788 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12547 BstLean.Part154.csC) ≤ 0.001020092181 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12547 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) ≤ 0.000194776017 ∧
    cc1 (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) ≤ 0.000123937250 ∧
    cc2 (rhoBar 12547 BstLean.Part154.csC) ≤ 0.000071946495 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12547 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12547 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12547 BstLean.Part154.csC * nuR (rhoBar 12547 BstLean.Part154.csC)) ≤ 0.000510029833 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255006788 : ℝ) * 0.001020092181 := by gcongr
      _ ≤ (0.000510029833 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12547 BstLean.Part154.csC) * nuR (rhoBar 12547 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020092181 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12547 BstLean.Part154.csC) * rhoBar 12547 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255006788 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255006788 / 2 + 0.399 * 0.001020092181 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194776017 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510029833 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123937250 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255006788 / 1.414213562 := by gcongr
      _ ≤ (0.000071946495 : ℝ) := by norm_num

end BstLean.Part269.N12547

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12547
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) ≤ 1.63835E-7 := by
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12547 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12547 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12547 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194776017 : ℝ) ^ 2 + 0.000123937250 ^ 2 + 3 * 0.000071946495 ^ 2 +
        2 * 0.797885 * 0.000194776017 * 0.000123937250 + 2 * 0.000194776017 * 0.000071946495 +
        4 * 0.797885 * 0.000123937250 * 0.000071946495 := by gcongr
    _ ≤ (1.63835E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12547 BstLean.Part154.csC Θ ≤ 0.002662486682 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12547 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12547 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12547 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036028817106 * 1.63835E-7 / (0.000255006393 : ℝ) := by gcongr
    _ ≤ 0.002662486682 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12547 BstLean.Part154.csC Θ ≤ 0.002954793270 + 0.000672765607 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12547 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12547 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036028817106 : ℝ) * ((2 * Θ * 0.000255006788 +
        (6863 / 10000) * 0.000255006788 * 12547 * 0.001020092181) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002954793270 + 0.000672765607 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12547 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12547 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12547 0.011 Θ ∧ gammaRatio 12547 0.011 Θ ≤ 0.000087664740 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12547 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036028817106 : ℝ) * 0.525 / ((1 - 0.011) * 12547) := by gcongr
      _ ≤ (0.000087664740 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12547 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12547 0.011 Θ) :=
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
    badAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12547 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12547 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12547 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12547 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12547 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12547 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12547 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12547 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12547 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12547 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036028817106 : ℝ) * 12547 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697835940 + 0.003335252289 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12547

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12547
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12547 BstLean.Part154.csC) (piBar (rhoBar 12547 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12547 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12547 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12547 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12547 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12547 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12547 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12547 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12547 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12547 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12547 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052806824387 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12547) ≤ 0.010661560722 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12547 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036028817106)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010661560722 + 2 * 0.737676 / 12547) := by gcongr
    _ ≤ (0.052806824387 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12547 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12547

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12547
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496564804 : ℝ) ≤ plow 12547 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12547) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955443392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397805509) : eMP 12547 0.011 xi bn ≤ 0.001203169164 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12547 : ℝ) * (1 - 0.011))) ≤ 0.000594881194 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397805509 / (12547 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594881194 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594881194 : ℝ) + 3.141593 * 0.052955443392 / (12547 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203169164 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955443392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397805509) : PiBarMP 12547 12 0.011 xi bn ≤ 0.162241345456 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12547 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037387237248 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.395614814946 : ℝ) ≤ √((12547 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.013392056485 : ℝ) ≤ √(12547 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12547) ≤ 0.124381629795 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037387237248 + 0.052955443392 * 1.772454 / (2 * (111.395614814946 : ℝ))) * (1 + 0.001203169164) +
        8 / (12547 * 112.013392056485) + 0.124381629795 := by gcongr
    _ ≤ (0.162241345456 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955443392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397805509) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282927321936) :
    parallelOracle 12547 0.011 xi bn cd ≤ 0.163244404686 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12547 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12547 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496564804 : ℝ) ≤ plow 12547 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.013392056485 : ℝ) ≤ √(12547 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282927321936 : ℝ) / (2 * 0.560496564804 * 112.013392056485)) * 0.162241345456 +
        0.282927321936 ^ 2 / (2 * 0.560496564804 * 112.013392056485) := by gcongr
    _ ≤ (0.163244404686 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955443392) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397805509)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282927321936) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12547 12547 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496564804 : ℝ) ≤ plow 12547 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.013392056485 : ℝ) ≤ √(12547 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12547 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12547 Θ 1.22 ≤ 0.011838767452 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.013392056485 := by gcongr <;> linarith
      _ ≤ (0.011838767452 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12547 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12547 12547 0.011 ≤ 0.008533685628 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12547 12547 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12547 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12547 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12547 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12547 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163244404686 + 0.011838767452 + (0.008533685628 : ℝ) *
        (1 + 2 * (0.282927321936 + 0.011838767452) / (0.560496564804 * 112.013392056485))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12547]

end BstLean.Part269.N12547

/-! The original eight local profiles supply actual 12547 moment certificates. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12547 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052955443392 ∧
    0 ≤ bN 12547 BstLean.Part154.csC (groupTheta g) ∧ bN 12547 BstLean.Part154.csC (groupTheta g) ≤ 0.001397805509 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12547 12547 0.011
      (momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12547 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12547 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12547 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230120497549 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12547 0.011
      (momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12547 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12547
/-! The actual computed-centre upper energy formula at 12547. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12547

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12547)
open BstLean.Part268 (cell12547)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085949825389
  | 2 => 0.086901329220
  | 3 => 0.087852299339
  | 4 => 0.088804455705
  | 5 => 0.089759868080
  | 6 => 0.090721006598
  | 7 => 0.091690796817
  | 8 => 0.092672679282
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12547 12547 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12547 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12547

/-! Actual upper energy certificates on all 43 source endpoints at 12547. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12547)
open BstLean.Part268 (cell12547)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12547 (gMinus 12547) (1 - (cell12547 i).lower) ≤ 1 ∧
    energyUpper 12547 (gMinus 12547) (BstLean.Part211.gPlus 12547)
      (finiteEnergy 12547 12547 0.011) (1 - (cell12547 i).lower) ≤
      (cell12547 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨10,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨11,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨12,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨13,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨14,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨15,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨16,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨17,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨18,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨19,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨20,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨21,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨22,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨23,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨24,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨25,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨26,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨27,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨28,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨29,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨30,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨31,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨32,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨33,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨34,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨35,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨36,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨37,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨38,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨39,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨40,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨41,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨42,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨43,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨44,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨45,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨46,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨47,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨48,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨49,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨50,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨51,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12547) (by norm_num)
        (q := 1 - (cell12547 ⟨52,by decide⟩).lower)
        (by norm_num [cell12547]) (by norm_num [cell12547])
      exact ⟨E.1,E.2.trans (by norm_num [cell12547])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12547

/-! Source-cell containment and simple scalar guards at 12547. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12547)
open BstLean.Part268 (cell12547)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12547 ⟨10,by decide⟩).lower ∧ (cell12547 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12547 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12547 ⟨11,by decide⟩).lower ∧ (cell12547 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12547 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12547 ⟨12,by decide⟩).lower ∧ (cell12547 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12547 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12547 ⟨13,by decide⟩).lower ∧ (cell12547 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12547 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12547 ⟨14,by decide⟩).lower ∧ (cell12547 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12547 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12547 ⟨15,by decide⟩).lower ∧ (cell12547 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12547 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12547 ⟨16,by decide⟩).lower ∧ (cell12547 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12547 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12547 ⟨17,by decide⟩).lower ∧ (cell12547 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12547 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12547 ⟨18,by decide⟩).lower ∧ (cell12547 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12547 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12547 ⟨19,by decide⟩).lower ∧ (cell12547 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12547 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12547 ⟨20,by decide⟩).lower ∧ (cell12547 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12547 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12547 ⟨21,by decide⟩).lower ∧ (cell12547 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12547 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12547 ⟨22,by decide⟩).lower ∧ (cell12547 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12547 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12547 ⟨23,by decide⟩).lower ∧ (cell12547 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12547 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12547 ⟨24,by decide⟩).lower ∧ (cell12547 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12547 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12547 ⟨25,by decide⟩).lower ∧ (cell12547 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12547 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12547 ⟨26,by decide⟩).lower ∧ (cell12547 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12547 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12547 ⟨27,by decide⟩).lower ∧ (cell12547 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12547 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12547 ⟨28,by decide⟩).lower ∧ (cell12547 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12547 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12547 ⟨29,by decide⟩).lower ∧ (cell12547 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12547 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12547 ⟨30,by decide⟩).lower ∧ (cell12547 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12547 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12547 ⟨31,by decide⟩).lower ∧ (cell12547 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12547 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12547 ⟨32,by decide⟩).lower ∧ (cell12547 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12547 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12547 ⟨33,by decide⟩).lower ∧ (cell12547 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12547 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12547 ⟨34,by decide⟩).lower ∧ (cell12547 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12547 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12547 ⟨35,by decide⟩).lower ∧ (cell12547 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12547 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12547 ⟨36,by decide⟩).lower ∧ (cell12547 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12547 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12547 ⟨37,by decide⟩).lower ∧ (cell12547 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12547 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12547 ⟨38,by decide⟩).lower ∧ (cell12547 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12547 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12547 ⟨39,by decide⟩).lower ∧ (cell12547 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12547 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12547 ⟨40,by decide⟩).lower ∧ (cell12547 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12547 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12547 ⟨41,by decide⟩).lower ∧ (cell12547 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12547 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12547 ⟨42,by decide⟩).lower ∧ (cell12547 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12547 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12547 ⟨43,by decide⟩).lower ∧ (cell12547 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12547 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12547 ⟨44,by decide⟩).lower ∧ (cell12547 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12547 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12547 ⟨45,by decide⟩).lower ∧ (cell12547 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12547 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12547 ⟨46,by decide⟩).lower ∧ (cell12547 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12547 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12547 ⟨47,by decide⟩).lower ∧ (cell12547 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12547 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12547 ⟨48,by decide⟩).lower ∧ (cell12547 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12547 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12547 ⟨49,by decide⟩).lower ∧ (cell12547 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12547 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12547 ⟨50,by decide⟩).lower ∧ (cell12547 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12547 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12547 ⟨51,by decide⟩).lower ∧ (cell12547 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12547 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12547 ⟨52,by decide⟩).lower ∧ (cell12547 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12547 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12547 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12547 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12547,cell12547,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12547 i).lower ∧
    (cell12547 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12547 i).upper ≤ (0.532 : ℝ) ∧
    (cell12547 i).centre ≤ (0.1 : ℝ) ∧ (cell12547 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12547 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12547 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12547

/-! The local source numeric instances at 12547 have no network premises. -/
namespace BstLean.Part269.N12547
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12547)
open BstLean.Part268 (cell12547)

noncomputable def sourceNumerics12547 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12547 (cell12547 i)
      scalarRow12547.M scalarRow12547.H scalarRow12547.xi := by
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
    energy_allowance := scalarRow12547.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12547]
    centre_nonneg := (scalarRow12547.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12547])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12547
/-! Actual 12548 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12548 ≤ (1.036027368735 : ℝ) := by
  have hr : (112.017855719523 : ℝ) ≤ √(12548 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.017855719523 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12548 12548 (11 / 1000) ≤
    (0.008533345577 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12548) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.017855719523 : ℝ) ≤ √(12548 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12548)
  have hdiv : K / √(12548 : ℝ) ≤ K / 112.017855719523 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.017855719523 ≤ (0.008533345577 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12548.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12548 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12548 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12548 := gPlus_lower 12548
end BstLean.Part269.N12548

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12548
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036027368734 : ℝ) ≤ wn 12548 := by
  have hn : √(12548 : ℝ) ≤ 112.017855719524 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12548 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.017855719524 ≤ 2 / √(12548 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254985714 : ℝ) ≤ rhoBar 12548 BstLean.Part154.csC ∧
    rhoBar 12548 BstLean.Part154.csC ≤ 0.000254986109 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036027368734 : ℝ) / (1.295212 * 12548) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036027368735 : ℝ) / (1.29521 * 12548) := by gcongr
      _ ≤ (0.000254986109 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12548 BstLean.Part154.csC) ≤ 0.001020009454 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12548 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) ≤ 0.000194760222 ∧
    cc1 (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) ≤ 0.000123927199 ∧
    cc2 (rhoBar 12548 BstLean.Part154.csC) ≤ 0.000071940661 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12548 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12548 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12548 BstLean.Part154.csC * nuR (rhoBar 12548 BstLean.Part154.csC)) ≤ 0.000509988473 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254986109 : ℝ) * 0.001020009454 := by gcongr
      _ ≤ (0.000509988473 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12548 BstLean.Part154.csC) * nuR (rhoBar 12548 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020009454 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12548 BstLean.Part154.csC) * rhoBar 12548 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254986109 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254986109 / 2 + 0.399 * 0.001020009454 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194760222 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509988473 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123927199 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254986109 / 1.414213562 := by gcongr
      _ ≤ (0.000071940661 : ℝ) := by norm_num

end BstLean.Part269.N12548

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12548
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) ≤ 1.63808E-7 := by
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12548 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12548 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12548 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194760222 : ℝ) ^ 2 + 0.000123927199 ^ 2 + 3 * 0.000071940661 ^ 2 +
        2 * 0.797885 * 0.000194760222 * 0.000123927199 + 2 * 0.000194760222 * 0.000071940661 +
        4 * 0.797885 * 0.000123927199 * 0.000071940661 := by gcongr
    _ ≤ (1.63808E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12548 BstLean.Part154.csC Θ ≤ 0.002662260071 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12548 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12548 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12548 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036027368735 * 1.63808E-7 / (0.000254985714 : ℝ) := by gcongr
    _ ≤ 0.002662260071 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12548 BstLean.Part154.csC Θ ≤ 0.002954545382 + 0.000672710111 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12548 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12548 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036027368735 : ℝ) * ((2 * Θ * 0.000254986109 +
        (6863 / 10000) * 0.000254986109 * 12548 * 0.001020009454) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002954545382 + 0.000672710111 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12548 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12548 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12548 0.011 Θ ∧ gammaRatio 12548 0.011 Θ ≤ 0.000087657631 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12548 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036027368735 : ℝ) * 0.525 / ((1 - 0.011) * 12548) := by gcongr
      _ ≤ (0.000087657631 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12548 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12548 0.011 Θ) :=
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
    badAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12548 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12548 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12548 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12548 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12548 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12548 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12548 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12548 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12548 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12548 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036027368735 : ℝ) * 12548 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697588052 + 0.003334970182 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12548

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12548
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12548 BstLean.Part154.csC) (piBar (rhoBar 12548 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12548 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12548 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12548 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12548 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12548 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12548 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12548 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12548 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12548 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12548 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052804697202 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12548) ≤ 0.010661135883 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12548 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036027368735)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010661135883 + 2 * 0.737676 / 12548) := by gcongr
    _ ≤ (0.052804697202 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12548 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12548

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12548
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496611133 : ℝ) ≤ plow 12548 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12548) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955047398)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397686538) : eMP 12548 0.011 xi bn ≤ 0.001203069955 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12548 : ℝ) * (1 - 0.011))) ≤ 0.000594832174 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397686538 / (12548 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594832174 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594832174 : ℝ) + 3.141593 * 0.052955047398 / (12548 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001203069955 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955047398)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397686538) : PiBarMP 12548 12 0.011 xi bn ≤ 0.162234771718 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12548 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037385646150 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.400053859951 : ℝ) ≤ √((12548 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.017855719523 : ℝ) ≤ √(12548 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12548) ≤ 0.124376673463 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037385646150 + 0.052955047398 * 1.772454 / (2 * (111.400053859951 : ℝ))) * (1 + 0.001203069955) +
        8 / (12548 * 112.017855719523) + 0.124376673463 := by gcongr
    _ ≤ (0.162234771718 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955047398)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397686538) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282924334344) :
    parallelOracle 12548 0.011 xi bn cd ≤ 0.163237758761 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12548 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12548 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496611133 : ℝ) ≤ plow 12548 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.017855719523 : ℝ) ≤ √(12548 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282924334344 : ℝ) / (2 * 0.560496611133 * 112.017855719523)) * 0.162234771718 +
        0.282924334344 ^ 2 / (2 * 0.560496611133 * 112.017855719523) := by gcongr
    _ ≤ (0.163237758761 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052955047398) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397686538)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282924334344) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12548 12548 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496611133 : ℝ) ≤ plow 12548 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.017855719523 : ℝ) ≤ √(12548 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12548 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12548 Θ 1.22 ≤ 0.011838295703 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.017855719523 := by gcongr <;> linarith
      _ ≤ (0.011838295703 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12548 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12548 12548 0.011 ≤ 0.008533345577 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12548 12548 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12548 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12548 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12548 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12548 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163237758761 + 0.011838295703 + (0.008533345577 : ℝ) *
        (1 + 2 * (0.282924334344 + 0.011838295703) / (0.560496611133 * 112.017855719523))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12548]

end BstLean.Part269.N12548

/-! The original eight local profiles supply actual 12548 moment certificates. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12548 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052955047398 ∧
    0 ≤ bN 12548 BstLean.Part154.csC (groupTheta g) ∧ bN 12548 BstLean.Part154.csC (groupTheta g) ≤ 0.001397686538 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12548 12548 0.011
      (momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12548 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12548 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12548 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230119637142 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12548 0.011
      (momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12548 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12548
/-! The actual computed-centre upper energy formula at 12548. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12548

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12548)
open BstLean.Part268 (cell12548)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085946730145
  | 2 => 0.086898172892
  | 3 => 0.087849072352
  | 4 => 0.088801146325
  | 5 => 0.089756462050
  | 6 => 0.090717486718
  | 7 => 0.091687142481
  | 8 => 0.092668865970
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12548 12548 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12548 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12548

/-! Actual upper energy certificates on all 43 source endpoints at 12548. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12548)
open BstLean.Part268 (cell12548)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12548 (gMinus 12548) (1 - (cell12548 i).lower) ≤ 1 ∧
    energyUpper 12548 (gMinus 12548) (BstLean.Part211.gPlus 12548)
      (finiteEnergy 12548 12548 0.011) (1 - (cell12548 i).lower) ≤
      (cell12548 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨10,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨11,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨12,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨13,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨14,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨15,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨16,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨17,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨18,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨19,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨20,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨21,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨22,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨23,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨24,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨25,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨26,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨27,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨28,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨29,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨30,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨31,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨32,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨33,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨34,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨35,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨36,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨37,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨38,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨39,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨40,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨41,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨42,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨43,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨44,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨45,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨46,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨47,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨48,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨49,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨50,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨51,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12548) (by norm_num)
        (q := 1 - (cell12548 ⟨52,by decide⟩).lower)
        (by norm_num [cell12548]) (by norm_num [cell12548])
      exact ⟨E.1,E.2.trans (by norm_num [cell12548])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12548

/-! Source-cell containment and simple scalar guards at 12548. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12548)
open BstLean.Part268 (cell12548)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12548 ⟨10,by decide⟩).lower ∧ (cell12548 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12548 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12548 ⟨11,by decide⟩).lower ∧ (cell12548 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12548 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12548 ⟨12,by decide⟩).lower ∧ (cell12548 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12548 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12548 ⟨13,by decide⟩).lower ∧ (cell12548 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12548 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12548 ⟨14,by decide⟩).lower ∧ (cell12548 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12548 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12548 ⟨15,by decide⟩).lower ∧ (cell12548 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12548 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12548 ⟨16,by decide⟩).lower ∧ (cell12548 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12548 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12548 ⟨17,by decide⟩).lower ∧ (cell12548 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12548 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12548 ⟨18,by decide⟩).lower ∧ (cell12548 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12548 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12548 ⟨19,by decide⟩).lower ∧ (cell12548 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12548 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12548 ⟨20,by decide⟩).lower ∧ (cell12548 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12548 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12548 ⟨21,by decide⟩).lower ∧ (cell12548 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12548 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12548 ⟨22,by decide⟩).lower ∧ (cell12548 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12548 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12548 ⟨23,by decide⟩).lower ∧ (cell12548 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12548 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12548 ⟨24,by decide⟩).lower ∧ (cell12548 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12548 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12548 ⟨25,by decide⟩).lower ∧ (cell12548 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12548 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12548 ⟨26,by decide⟩).lower ∧ (cell12548 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12548 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12548 ⟨27,by decide⟩).lower ∧ (cell12548 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12548 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12548 ⟨28,by decide⟩).lower ∧ (cell12548 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12548 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12548 ⟨29,by decide⟩).lower ∧ (cell12548 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12548 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12548 ⟨30,by decide⟩).lower ∧ (cell12548 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12548 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12548 ⟨31,by decide⟩).lower ∧ (cell12548 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12548 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12548 ⟨32,by decide⟩).lower ∧ (cell12548 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12548 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12548 ⟨33,by decide⟩).lower ∧ (cell12548 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12548 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12548 ⟨34,by decide⟩).lower ∧ (cell12548 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12548 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12548 ⟨35,by decide⟩).lower ∧ (cell12548 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12548 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12548 ⟨36,by decide⟩).lower ∧ (cell12548 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12548 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12548 ⟨37,by decide⟩).lower ∧ (cell12548 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12548 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12548 ⟨38,by decide⟩).lower ∧ (cell12548 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12548 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12548 ⟨39,by decide⟩).lower ∧ (cell12548 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12548 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12548 ⟨40,by decide⟩).lower ∧ (cell12548 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12548 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12548 ⟨41,by decide⟩).lower ∧ (cell12548 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12548 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12548 ⟨42,by decide⟩).lower ∧ (cell12548 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12548 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12548 ⟨43,by decide⟩).lower ∧ (cell12548 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12548 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12548 ⟨44,by decide⟩).lower ∧ (cell12548 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12548 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12548 ⟨45,by decide⟩).lower ∧ (cell12548 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12548 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12548 ⟨46,by decide⟩).lower ∧ (cell12548 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12548 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12548 ⟨47,by decide⟩).lower ∧ (cell12548 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12548 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12548 ⟨48,by decide⟩).lower ∧ (cell12548 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12548 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12548 ⟨49,by decide⟩).lower ∧ (cell12548 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12548 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12548 ⟨50,by decide⟩).lower ∧ (cell12548 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12548 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12548 ⟨51,by decide⟩).lower ∧ (cell12548 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12548 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12548 ⟨52,by decide⟩).lower ∧ (cell12548 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12548 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12548 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12548 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12548,cell12548,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12548 i).lower ∧
    (cell12548 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12548 i).upper ≤ (0.532 : ℝ) ∧
    (cell12548 i).centre ≤ (0.1 : ℝ) ∧ (cell12548 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12548 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12548 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12548

/-! The local source numeric instances at 12548 have no network premises. -/
namespace BstLean.Part269.N12548
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12548)
open BstLean.Part268 (cell12548)

noncomputable def sourceNumerics12548 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12548 (cell12548 i)
      scalarRow12548.M scalarRow12548.H scalarRow12548.xi := by
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
    energy_allowance := scalarRow12548.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12548]
    centre_nonneg := (scalarRow12548.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12548])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12548
/-! Actual 12549 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12549 ≤ (1.036025920537 : ℝ) := by
  have hr : (112.022319204701 : ℝ) ≤ √(12549 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.022319204701 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12549 12549 (11 / 1000) ≤
    (0.008533005566 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12549) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.022319204701 : ℝ) ≤ √(12549 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12549)
  have hdiv : K / √(12549 : ℝ) ≤ K / 112.022319204701 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.022319204701 ≤ (0.008533005566 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12549.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12549 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12549 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12549 := gPlus_lower 12549
end BstLean.Part269.N12549

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12549
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036025920536 : ℝ) ≤ wn 12549 := by
  have hn : √(12549 : ℝ) ≤ 112.022319204702 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12549 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.022319204702 ≤ 2 / √(12549 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254965039 : ℝ) ≤ rhoBar 12549 BstLean.Part154.csC ∧
    rhoBar 12549 BstLean.Part154.csC ≤ 0.000254965433 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036025920536 : ℝ) / (1.295212 * 12549) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036025920537 : ℝ) / (1.29521 * 12549) := by gcongr
      _ ≤ (0.000254965433 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12549 BstLean.Part154.csC) ≤ 0.001019926740 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12549 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) ≤ 0.000194744429 ∧
    cc1 (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) ≤ 0.000123917150 ∧
    cc2 (rhoBar 12549 BstLean.Part154.csC) ≤ 0.000071934827 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12549 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12549 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12549 BstLean.Part154.csC * nuR (rhoBar 12549 BstLean.Part154.csC)) ≤ 0.000509947118 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254965433 : ℝ) * 0.001019926740 := by gcongr
      _ ≤ (0.000509947118 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12549 BstLean.Part154.csC) * nuR (rhoBar 12549 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019926740 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12549 BstLean.Part154.csC) * rhoBar 12549 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254965433 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254965433 / 2 + 0.399 * 0.001019926740 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194744429 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509947118 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123917150 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254965433 / 1.414213562 := by gcongr
      _ ≤ (0.000071934827 : ℝ) := by norm_num

end BstLean.Part269.N12549

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12549
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) ≤ 1.63782E-7 := by
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12549 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12549 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12549 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194744429 : ℝ) ^ 2 + 0.000123917150 ^ 2 + 3 * 0.000071934827 ^ 2 +
        2 * 0.797885 * 0.000194744429 * 0.000123917150 + 2 * 0.000194744429 * 0.000071934827 +
        4 * 0.797885 * 0.000123917150 * 0.000071934827 := by gcongr
    _ ≤ (1.63782E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12549 BstLean.Part154.csC Θ ≤ 0.002662049637 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12549 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12549 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12549 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036025920537 * 1.63782E-7 / (0.000254965039 : ℝ) := by gcongr
    _ ≤ 0.002662049637 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12549 BstLean.Part154.csC Θ ≤ 0.002954297530 + 0.000672654623 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12549 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12549 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036025920537 : ℝ) * ((2 * Θ * 0.000254965433 +
        (6863 / 10000) * 0.000254965433 * 12549 * 0.001019926740) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002954297530 + 0.000672654623 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12549 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12549 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12549 0.011 Θ ∧ gammaRatio 12549 0.011 Θ ≤ 0.000087650523 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12549 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036025920537 : ℝ) * 0.525 / ((1 - 0.011) * 12549) := by gcongr
      _ ≤ (0.000087650523 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12549 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12549 0.011 Θ) :=
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
    badAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12549 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12549 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12549 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12549 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12549 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12549 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12549 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12549 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12549 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12549 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036025920537 : ℝ) * 12549 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697340200 + 0.003334704260 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12549

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12549
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12549 BstLean.Part154.csC) (piBar (rhoBar 12549 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12549 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12549 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12549 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12549 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12549 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12549 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12549 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12549 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12549 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12549 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052802570269 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12549) ≤ 0.010660711094 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12549 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036025920537)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010660711094 + 2 * 0.737676 / 12549) := by gcongr
    _ ≤ (0.052802570269 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12549 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12549

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12549
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496657454 : ℝ) ≤ plow 12549 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12549) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954659937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397576060) : eMP 12549 0.011 xi bn ≤ 0.001202974371 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12549 : ℝ) * (1 - 0.011))) ≤ 0.000594784965 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397576060 / (12549 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594784965 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594784965 : ℝ) + 3.141593 * 0.052954659937 / (12549 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202974371 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954659937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397576060) : PiBarMP 12549 12 0.011 xi bn ≤ 0.162228312440 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12549 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037384168575 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.404492728076 : ℝ) ≤ √((12549 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.022319204701 : ℝ) ≤ √(12549 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12549) ≤ 0.124371717723 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037384168575 + 0.052954659937 * 1.772454 / (2 * (111.404492728076 : ℝ))) * (1 + 0.001202974371) +
        8 / (12549 * 112.022319204701) + 0.124371717723 := by gcongr
    _ ≤ (0.162228312440 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954659937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397576060) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282921365541) :
    parallelOracle 12549 0.011 xi bn cd ≤ 0.163231227671 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12549 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12549 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496657454 : ℝ) ≤ plow 12549 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.022319204701 : ℝ) ≤ √(12549 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282921365541 : ℝ) / (2 * 0.560496657454 * 112.022319204701)) * 0.162228312440 +
        0.282921365541 ^ 2 / (2 * 0.560496657454 * 112.022319204701) := by gcongr
    _ ≤ (0.163231227671 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954659937) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397576060)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282921365541) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12549 12549 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496657454 : ℝ) ≤ plow 12549 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.022319204701 : ℝ) ≤ √(12549 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12549 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12549 Θ 1.22 ≤ 0.011837824011 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.022319204701 := by gcongr <;> linarith
      _ ≤ (0.011837824011 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12549 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12549 12549 0.011 ≤ 0.008533005566 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12549 12549 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12549 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12549 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12549 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12549 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163231227671 + 0.011837824011 + (0.008533005566 : ℝ) *
        (1 + 2 * (0.282921365541 + 0.011837824011) / (0.560496657454 * 112.022319204701))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12549]

end BstLean.Part269.N12549

/-! The original eight local profiles supply actual 12549 moment certificates. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12549 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052954659937 ∧
    0 ≤ bN 12549 BstLean.Part154.csC (groupTheta g) ∧ bN 12549 BstLean.Part154.csC (groupTheta g) ≤ 0.001397576060 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12549 12549 0.011
      (momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12549 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12549 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12549 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230118795272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12549 0.011
      (momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12549 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12549
/-! The actual computed-centre upper energy formula at 12549. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12549

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12549)
open BstLean.Part268 (cell12549)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085943636169
  | 2 => 0.086895017887
  | 3 => 0.087845846753
  | 4 => 0.088797838417
  | 5 => 0.089753057592
  | 6 => 0.090713968531
  | 7 => 0.091683489986
  | 8 => 0.092665054674
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12549 12549 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12549 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12549

/-! Actual upper energy certificates on all 43 source endpoints at 12549. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12549)
open BstLean.Part268 (cell12549)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12549 (gMinus 12549) (1 - (cell12549 i).lower) ≤ 1 ∧
    energyUpper 12549 (gMinus 12549) (BstLean.Part211.gPlus 12549)
      (finiteEnergy 12549 12549 0.011) (1 - (cell12549 i).lower) ≤
      (cell12549 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨10,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨11,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨12,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨13,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨14,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨15,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨16,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨17,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨18,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨19,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨20,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨21,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨22,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨23,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨24,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨25,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨26,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨27,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨28,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨29,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨30,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨31,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨32,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨33,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨34,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨35,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨36,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨37,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨38,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨39,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨40,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨41,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨42,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨43,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨44,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨45,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨46,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨47,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨48,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨49,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨50,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨51,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12549) (by norm_num)
        (q := 1 - (cell12549 ⟨52,by decide⟩).lower)
        (by norm_num [cell12549]) (by norm_num [cell12549])
      exact ⟨E.1,E.2.trans (by norm_num [cell12549])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12549

/-! Source-cell containment and simple scalar guards at 12549. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12549)
open BstLean.Part268 (cell12549)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12549 ⟨10,by decide⟩).lower ∧ (cell12549 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12549 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12549 ⟨11,by decide⟩).lower ∧ (cell12549 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12549 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12549 ⟨12,by decide⟩).lower ∧ (cell12549 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12549 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12549 ⟨13,by decide⟩).lower ∧ (cell12549 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12549 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12549 ⟨14,by decide⟩).lower ∧ (cell12549 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12549 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12549 ⟨15,by decide⟩).lower ∧ (cell12549 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12549 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12549 ⟨16,by decide⟩).lower ∧ (cell12549 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12549 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12549 ⟨17,by decide⟩).lower ∧ (cell12549 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12549 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12549 ⟨18,by decide⟩).lower ∧ (cell12549 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12549 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12549 ⟨19,by decide⟩).lower ∧ (cell12549 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12549 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12549 ⟨20,by decide⟩).lower ∧ (cell12549 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12549 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12549 ⟨21,by decide⟩).lower ∧ (cell12549 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12549 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12549 ⟨22,by decide⟩).lower ∧ (cell12549 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12549 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12549 ⟨23,by decide⟩).lower ∧ (cell12549 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12549 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12549 ⟨24,by decide⟩).lower ∧ (cell12549 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12549 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12549 ⟨25,by decide⟩).lower ∧ (cell12549 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12549 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12549 ⟨26,by decide⟩).lower ∧ (cell12549 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12549 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12549 ⟨27,by decide⟩).lower ∧ (cell12549 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12549 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12549 ⟨28,by decide⟩).lower ∧ (cell12549 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12549 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12549 ⟨29,by decide⟩).lower ∧ (cell12549 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12549 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12549 ⟨30,by decide⟩).lower ∧ (cell12549 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12549 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12549 ⟨31,by decide⟩).lower ∧ (cell12549 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12549 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12549 ⟨32,by decide⟩).lower ∧ (cell12549 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12549 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12549 ⟨33,by decide⟩).lower ∧ (cell12549 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12549 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12549 ⟨34,by decide⟩).lower ∧ (cell12549 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12549 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12549 ⟨35,by decide⟩).lower ∧ (cell12549 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12549 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12549 ⟨36,by decide⟩).lower ∧ (cell12549 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12549 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12549 ⟨37,by decide⟩).lower ∧ (cell12549 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12549 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12549 ⟨38,by decide⟩).lower ∧ (cell12549 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12549 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12549 ⟨39,by decide⟩).lower ∧ (cell12549 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12549 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12549 ⟨40,by decide⟩).lower ∧ (cell12549 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12549 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12549 ⟨41,by decide⟩).lower ∧ (cell12549 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12549 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12549 ⟨42,by decide⟩).lower ∧ (cell12549 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12549 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12549 ⟨43,by decide⟩).lower ∧ (cell12549 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12549 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12549 ⟨44,by decide⟩).lower ∧ (cell12549 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12549 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12549 ⟨45,by decide⟩).lower ∧ (cell12549 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12549 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12549 ⟨46,by decide⟩).lower ∧ (cell12549 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12549 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12549 ⟨47,by decide⟩).lower ∧ (cell12549 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12549 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12549 ⟨48,by decide⟩).lower ∧ (cell12549 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12549 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12549 ⟨49,by decide⟩).lower ∧ (cell12549 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12549 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12549 ⟨50,by decide⟩).lower ∧ (cell12549 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12549 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12549 ⟨51,by decide⟩).lower ∧ (cell12549 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12549 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12549 ⟨52,by decide⟩).lower ∧ (cell12549 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12549 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12549 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12549 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12549,cell12549,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12549 i).lower ∧
    (cell12549 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12549 i).upper ≤ (0.532 : ℝ) ∧
    (cell12549 i).centre ≤ (0.1 : ℝ) ∧ (cell12549 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12549 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12549 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12549

/-! The local source numeric instances at 12549 have no network premises. -/
namespace BstLean.Part269.N12549
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12549)
open BstLean.Part268 (cell12549)

noncomputable def sourceNumerics12549 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12549 (cell12549 i)
      scalarRow12549.M scalarRow12549.H scalarRow12549.xi := by
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
    energy_allowance := scalarRow12549.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12549]
    centre_nonneg := (scalarRow12549.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12549])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12549