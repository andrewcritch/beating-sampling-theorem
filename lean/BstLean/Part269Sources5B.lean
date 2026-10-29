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
import BstLean.Part269Direction5
import BstLean.Part269Shared5
import BstLean.Part269Finite
import BstLean.Part269Rows5
import BstLean.Part269Source
/-! Actual 12488 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12488 ≤ (1.036114580512 : ℝ) := by
  have hr : (111.749720357591 : ℝ) ≤ √(12488 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.749720357591 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12488 12488 (11 / 1000) ≤
    (0.008553820882 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12488) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.749720357591 : ℝ) ≤ √(12488 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12488)
  have hdiv : K / √(12488 : ℝ) ≤ K / 111.749720357591 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.749720357591 ≤ (0.008553820882 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12488.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12488 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12488 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12488 := gPlus_lower 12488
end BstLean.Part269.N12488

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12488
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036114580511 : ℝ) ≤ wn 12488 := by
  have hn : √(12488 : ℝ) ≤ 111.749720357592 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12488 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.749720357592 ≤ 2 / √(12488 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256232389 : ℝ) ≤ rhoBar 12488 BstLean.Part154.csC ∧
    rhoBar 12488 BstLean.Part154.csC ≤ 0.000256232786 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036114580511 : ℝ) / (1.295212 * 12488) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036114580512 : ℝ) / (1.29521 * 12488) := by gcongr
      _ ≤ (0.000256232786 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12488 BstLean.Part154.csC) ≤ 0.001024996800 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12488 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) ≤ 0.000195712488 ∧
    cc1 (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) ≤ 0.000124533123 ∧
    cc2 (rhoBar 12488 BstLean.Part154.csC) ≤ 0.000072292393 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12488 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12488 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12488 BstLean.Part154.csC * nuR (rhoBar 12488 BstLean.Part154.csC)) ≤ 0.000512481986 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256232786 : ℝ) * 0.001024996800 := by gcongr
      _ ≤ (0.000512481986 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12488 BstLean.Part154.csC) * nuR (rhoBar 12488 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024996800 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12488 BstLean.Part154.csC) * rhoBar 12488 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256232786 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256232786 / 2 + 0.399 * 0.001024996800 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195712488 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512481986 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124533123 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256232786 / 1.414213562 := by gcongr
      _ ≤ (0.000072292393 : ℝ) := by norm_num

end BstLean.Part269.N12488

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12488
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) ≤ 1.65414E-7 := by
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12488 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12488 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12488 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195712488 : ℝ) ^ 2 + 0.000124533123 ^ 2 + 3 * 0.000072292393 ^ 2 +
        2 * 0.797885 * 0.000195712488 * 0.000124533123 + 2 * 0.000195712488 * 0.000072292393 +
        4 * 0.797885 * 0.000124533123 * 0.000072292393 := by gcongr
    _ ≤ (1.65414E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12488 BstLean.Part154.csC Θ ≤ 0.002675506526 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12488 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12488 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12488 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036114580512 * 1.65414E-7 / (0.000256232389 : ℝ) := by gcongr
    _ ≤ 0.002675506526 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12488 BstLean.Part154.csC Θ ≤ 0.002969491534 + 0.000676056027 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12488 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12488 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036114580512 : ℝ) * ((2 * Θ * 0.000256232786 +
        (6863 / 10000) * 0.000256232786 * 12488 * 0.001024996800) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002969491534 + 0.000676056027 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12488 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12488 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12488 0.011 Θ ∧ gammaRatio 12488 0.011 Θ ≤ 0.000088086206 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12488 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036114580512 : ℝ) * 0.525 / ((1 - 0.011) * 12488) := by gcongr
      _ ≤ (0.000088086206 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12488 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12488 0.011 Θ) :=
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
    badAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12488 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12488 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12488 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12488 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12488 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12488 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12488 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12488 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12488 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12488 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036114580512 : ℝ) * 12488 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003786830696 + 0.003351562553 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12488

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12488
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12488 BstLean.Part154.csC) (piBar (rhoBar 12488 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12488 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12488 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12488 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12488 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12488 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12488 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12488 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12488 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12488 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12488 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052932783647 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12488) ≤ 0.010686716506 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12488 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036114580512)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010686716506 + 2 * 0.737676 / 12488) := by gcongr
    _ ≤ (0.052932783647 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12488 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12488

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12488
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493818265 : ℝ) ≤ plow 12488 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12488) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053001037)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404640927) : eMP 12488 0.011 xi bn ≤ 0.001208976886 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12488 : ℝ) * (1 - 0.011))) ≤ 0.000597740977 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404640927 / (12488 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597740977 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597740977 : ℝ) + 3.141593 * 0.053053001037 / (12488 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208976886 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053001037)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404640927) : PiBarMP 12488 12 0.011 xi bn ≤ 0.162628268752 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12488 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037478539553 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.133397320517 : ℝ) ≤ √((12488 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.749720357591 : ℝ) ≤ √(12488 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12488) ≤ 0.124675106284 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037478539553 + 0.053053001037 * 1.772454 / (2 * (111.133397320517 : ℝ))) * (1 + 0.001208976886) +
        8 / (12488 * 111.749720357591) + 0.124675106284 := by gcongr
    _ ≤ (0.162628268752 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053001037)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404640927) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283265154445) :
    parallelOracle 12488 0.011 xi bn cd ≤ 0.163636539001 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12488 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12488 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493818265 : ℝ) ≤ plow 12488 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.749720357591 : ℝ) ≤ √(12488 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283265154445 : ℝ) / (2 * 0.560493818265 * 111.749720357591)) * 0.162628268752 +
        0.283265154445 ^ 2 / (2 * 0.560493818265 * 111.749720357591) := by gcongr
    _ ≤ (0.163636539001 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053001037) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404640927)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283265154445) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12488 12488 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493818265 : ℝ) ≤ plow 12488 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.749720357591 : ℝ) ≤ √(12488 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12488 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12488 Θ 1.22 ≤ 0.011866700837 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.749720357591 := by gcongr <;> linarith
      _ ≤ (0.011866700837 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12488 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12488 12488 0.011 ≤ 0.008553820882 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12488 12488 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12488 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12488 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12488 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12488 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163636539001 + 0.011866700837 + (0.008553820882 : ℝ) *
        (1 + 2 * (0.283265154445 + 0.011866700837) / (0.560493818265 * 111.749720357591))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12488]

end BstLean.Part269.N12488

/-! The original eight local profiles supply actual 12488 moment certificates. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12488 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053053001037 ∧
    0 ≤ bN 12488 BstLean.Part154.csC (groupTheta g) ∧ bN 12488 BstLean.Part154.csC (groupTheta g) ≤ 0.001404640927 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12488 12488 0.011
      (momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12488 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12488 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12488 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230332370798 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12488 0.011
      (momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12488 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12488
/-! The actual computed-centre upper energy formula at 12488. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12488

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12488)
open BstLean.Part268 (cell12488)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086134738870
  | 2 => 0.087089945202
  | 3 => 0.088045205941
  | 4 => 0.089002372760
  | 5 => 0.089963669733
  | 6 => 0.090931746587
  | 7 => 0.091909736571
  | 8 => 0.092901318949
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12488 12488 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12488 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12488

/-! Actual upper energy certificates on all 43 source endpoints at 12488. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12488)
open BstLean.Part268 (cell12488)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12488 (gMinus 12488) (1 - (cell12488 i).lower) ≤ 1 ∧
    energyUpper 12488 (gMinus 12488) (BstLean.Part211.gPlus 12488)
      (finiteEnergy 12488 12488 0.011) (1 - (cell12488 i).lower) ≤
      (cell12488 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨10,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨11,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨12,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨13,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨14,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨15,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨16,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨17,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨18,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨19,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨20,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨21,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨22,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨23,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨24,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨25,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨26,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨27,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨28,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨29,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨30,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨31,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨32,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨33,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨34,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨35,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨36,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨37,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨38,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨39,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨40,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨41,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨42,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨43,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨44,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨45,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨46,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨47,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨48,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨49,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨50,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨51,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12488) (by norm_num)
        (q := 1 - (cell12488 ⟨52,by decide⟩).lower)
        (by norm_num [cell12488]) (by norm_num [cell12488])
      exact ⟨E.1,E.2.trans (by norm_num [cell12488])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12488

/-! Source-cell containment and simple scalar guards at 12488. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12488)
open BstLean.Part268 (cell12488)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12488 ⟨10,by decide⟩).lower ∧ (cell12488 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12488 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12488 ⟨11,by decide⟩).lower ∧ (cell12488 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12488 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12488 ⟨12,by decide⟩).lower ∧ (cell12488 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12488 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12488 ⟨13,by decide⟩).lower ∧ (cell12488 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12488 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12488 ⟨14,by decide⟩).lower ∧ (cell12488 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12488 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12488 ⟨15,by decide⟩).lower ∧ (cell12488 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12488 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12488 ⟨16,by decide⟩).lower ∧ (cell12488 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12488 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12488 ⟨17,by decide⟩).lower ∧ (cell12488 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12488 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12488 ⟨18,by decide⟩).lower ∧ (cell12488 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12488 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12488 ⟨19,by decide⟩).lower ∧ (cell12488 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12488 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12488 ⟨20,by decide⟩).lower ∧ (cell12488 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12488 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12488 ⟨21,by decide⟩).lower ∧ (cell12488 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12488 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12488 ⟨22,by decide⟩).lower ∧ (cell12488 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12488 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12488 ⟨23,by decide⟩).lower ∧ (cell12488 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12488 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12488 ⟨24,by decide⟩).lower ∧ (cell12488 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12488 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12488 ⟨25,by decide⟩).lower ∧ (cell12488 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12488 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12488 ⟨26,by decide⟩).lower ∧ (cell12488 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12488 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12488 ⟨27,by decide⟩).lower ∧ (cell12488 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12488 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12488 ⟨28,by decide⟩).lower ∧ (cell12488 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12488 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12488 ⟨29,by decide⟩).lower ∧ (cell12488 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12488 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12488 ⟨30,by decide⟩).lower ∧ (cell12488 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12488 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12488 ⟨31,by decide⟩).lower ∧ (cell12488 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12488 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12488 ⟨32,by decide⟩).lower ∧ (cell12488 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12488 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12488 ⟨33,by decide⟩).lower ∧ (cell12488 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12488 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12488 ⟨34,by decide⟩).lower ∧ (cell12488 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12488 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12488 ⟨35,by decide⟩).lower ∧ (cell12488 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12488 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12488 ⟨36,by decide⟩).lower ∧ (cell12488 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12488 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12488 ⟨37,by decide⟩).lower ∧ (cell12488 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12488 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12488 ⟨38,by decide⟩).lower ∧ (cell12488 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12488 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12488 ⟨39,by decide⟩).lower ∧ (cell12488 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12488 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12488 ⟨40,by decide⟩).lower ∧ (cell12488 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12488 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12488 ⟨41,by decide⟩).lower ∧ (cell12488 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12488 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12488 ⟨42,by decide⟩).lower ∧ (cell12488 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12488 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12488 ⟨43,by decide⟩).lower ∧ (cell12488 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12488 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12488 ⟨44,by decide⟩).lower ∧ (cell12488 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12488 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12488 ⟨45,by decide⟩).lower ∧ (cell12488 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12488 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12488 ⟨46,by decide⟩).lower ∧ (cell12488 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12488 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12488 ⟨47,by decide⟩).lower ∧ (cell12488 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12488 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12488 ⟨48,by decide⟩).lower ∧ (cell12488 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12488 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12488 ⟨49,by decide⟩).lower ∧ (cell12488 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12488 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12488 ⟨50,by decide⟩).lower ∧ (cell12488 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12488 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12488 ⟨51,by decide⟩).lower ∧ (cell12488 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12488 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12488 ⟨52,by decide⟩).lower ∧ (cell12488 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12488 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12488 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12488 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12488,cell12488,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12488 i).lower ∧
    (cell12488 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12488 i).upper ≤ (0.532 : ℝ) ∧
    (cell12488 i).centre ≤ (0.1 : ℝ) ∧ (cell12488 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12488 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12488 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12488

/-! The local source numeric instances at 12488 have no network premises. -/
namespace BstLean.Part269.N12488
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12488)
open BstLean.Part268 (cell12488)

noncomputable def sourceNumerics12488 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12488 (cell12488 i)
      scalarRow12488.M scalarRow12488.H scalarRow12488.xi := by
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
    energy_allowance := scalarRow12488.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12488]
    centre_nonneg := (scalarRow12488.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12488])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12488
/-! Actual 12489 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12489 ≤ (1.036113121804 : ℝ) := by
  have hr : (111.754194552150 : ℝ) ≤ √(12489 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.754194552150 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12489 12489 (11 / 1000) ≤
    (0.008553478418 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12489) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.754194552150 : ℝ) ≤ √(12489 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12489)
  have hdiv : K / √(12489 : ℝ) ≤ K / 111.754194552150 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.754194552150 ≤ (0.008553478418 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12489.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12489 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12489 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12489 := gPlus_lower 12489
end BstLean.Part269.N12489

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12489
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036113121803 : ℝ) ≤ wn 12489 := by
  have hn : √(12489 : ℝ) ≤ 111.754194552151 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12489 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.754194552151 ≤ 2 / √(12489 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256211512 : ℝ) ≤ rhoBar 12489 BstLean.Part154.csC ∧
    rhoBar 12489 BstLean.Part154.csC ≤ 0.000256211909 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036113121803 : ℝ) / (1.295212 * 12489) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036113121804 : ℝ) / (1.29521 * 12489) := by gcongr
      _ ≤ (0.000256211909 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12489 BstLean.Part154.csC) ≤ 0.001024913281 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12489 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) ≤ 0.000195696541 ∧
    cc1 (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) ≤ 0.000124522976 ∧
    cc2 (rhoBar 12489 BstLean.Part154.csC) ≤ 0.000072286503 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12489 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12489 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12489 BstLean.Part154.csC * nuR (rhoBar 12489 BstLean.Part154.csC)) ≤ 0.000512440229 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256211909 : ℝ) * 0.001024913281 := by gcongr
      _ ≤ (0.000512440229 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12489 BstLean.Part154.csC) * nuR (rhoBar 12489 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024913281 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12489 BstLean.Part154.csC) * rhoBar 12489 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256211909 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256211909 / 2 + 0.399 * 0.001024913281 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195696541 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512440229 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124522976 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256211909 / 1.414213562 := by gcongr
      _ ≤ (0.000072286503 : ℝ) := by norm_num

end BstLean.Part269.N12489

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12489
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) ≤ 1.65387E-7 := by
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12489 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12489 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12489 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195696541 : ℝ) ^ 2 + 0.000124522976 ^ 2 + 3 * 0.000072286503 ^ 2 +
        2 * 0.797885 * 0.000195696541 * 0.000124522976 + 2 * 0.000195696541 * 0.000072286503 +
        4 * 0.797885 * 0.000124522976 * 0.000072286503 := by gcongr
    _ ≤ (1.65387E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12489 BstLean.Part154.csC Θ ≤ 0.002675284019 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12489 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12489 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12489 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036113121804 * 1.65387E-7 / (0.000256211512 : ℝ) := by gcongr
    _ ≤ 0.002675284019 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12489 BstLean.Part154.csC Θ ≤ 0.002969241217 + 0.000675999993 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12489 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12489 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036113121804 : ℝ) * ((2 * Θ * 0.000256211909 +
        (6863 / 10000) * 0.000256211909 * 12489 * 0.001024913281) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002969241217 + 0.000675999993 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12489 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12489 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12489 0.011 Θ ∧ gammaRatio 12489 0.011 Θ ≤ 0.000088079029 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12489 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036113121804 : ℝ) * 0.525 / ((1 - 0.011) * 12489) := by gcongr
      _ ≤ (0.000088079029 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12489 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12489 0.011 Θ) :=
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
    badAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12489 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12489 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12489 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12489 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12489 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12489 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12489 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12489 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12489 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12489 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036113121804 : ℝ) * 12489 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003786580379 + 0.003351284012 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12489

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12489
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12489 BstLean.Part154.csC) (piBar (rhoBar 12489 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12489 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12489 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12489 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12489 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12489 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12489 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12489 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12489 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12489 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12489 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052930641256 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12489) ≤ 0.010686288652 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12489 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036113121804)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010686288652 + 2 * 0.737676 / 12489) := by gcongr
    _ ≤ (0.052930641256 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12489 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12489

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12489
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493865033 : ℝ) ≤ plow 12489 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12489) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052604486)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404524110) : eMP 12489 0.011 xi bn ≤ 0.001208878133 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12489 : ℝ) * (1 - 0.011))) ≤ 0.000597692191 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404524110 / (12489 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597692191 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597692191 : ℝ) + 3.141593 * 0.053052604486 / (12489 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208878133 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052604486)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404524110) : PiBarMP 12489 12 0.011 xi bn ≤ 0.162621692333 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12489 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037476981069 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.137846838959 : ℝ) ≤ √((12489 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.754194552150 : ℝ) ≤ √(12489 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12489) ≤ 0.124670114788 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037476981069 + 0.053052604486 * 1.772454 / (2 * (111.137846838959 : ℝ))) * (1 + 0.001208878133) +
        8 / (12489 * 111.754194552150) + 0.124670114788 := by gcongr
    _ ≤ (0.162621692333 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052604486)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404524110) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283262151229) :
    parallelOracle 12489 0.011 xi bn cd ≤ 0.163629889781 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12489 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12489 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493865033 : ℝ) ≤ plow 12489 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.754194552150 : ℝ) ≤ √(12489 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283262151229 : ℝ) / (2 * 0.560493865033 * 111.754194552150)) * 0.162621692333 +
        0.283262151229 ^ 2 / (2 * 0.560493865033 * 111.754194552150) := by gcongr
    _ ≤ (0.163629889781 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052604486) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404524110)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283262151229) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12489 12489 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493865033 : ℝ) ≤ plow 12489 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.754194552150 : ℝ) ≤ √(12489 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12489 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12489 Θ 1.22 ≤ 0.011866225741 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.754194552150 := by gcongr <;> linarith
      _ ≤ (0.011866225741 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12489 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12489 12489 0.011 ≤ 0.008553478418 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12489 12489 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12489 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12489 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12489 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12489 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163629889781 + 0.011866225741 + (0.008553478418 : ℝ) *
        (1 + 2 * (0.283262151229 + 0.011866225741) / (0.560493865033 * 111.754194552150))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12489]

end BstLean.Part269.N12489

/-! The original eight local profiles supply actual 12489 moment certificates. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12489 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053052604486 ∧
    0 ≤ bN 12489 BstLean.Part154.csC (groupTheta g) ∧ bN 12489 BstLean.Part154.csC (groupTheta g) ≤ 0.001404524110 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12489 12489 0.011
      (momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12489 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12489 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12489 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230331509973 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12489 0.011
      (momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12489 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12489
/-! The actual computed-centre upper energy formula at 12489. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12489

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12489)
open BstLean.Part268 (cell12489)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086131566364
  | 2 => 0.087086708284
  | 3 => 0.088041894256
  | 4 => 0.088998973642
  | 5 => 0.089960167815
  | 6 => 0.090928123355
  | 7 => 0.091905969878
  | 8 => 0.092897382473
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12489 12489 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12489 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12489

/-! Actual upper energy certificates on all 43 source endpoints at 12489. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12489)
open BstLean.Part268 (cell12489)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12489 (gMinus 12489) (1 - (cell12489 i).lower) ≤ 1 ∧
    energyUpper 12489 (gMinus 12489) (BstLean.Part211.gPlus 12489)
      (finiteEnergy 12489 12489 0.011) (1 - (cell12489 i).lower) ≤
      (cell12489 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨10,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨11,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨12,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨13,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨14,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨15,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨16,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨17,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨18,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨19,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨20,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨21,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨22,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨23,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨24,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨25,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨26,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨27,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨28,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨29,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨30,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨31,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨32,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨33,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨34,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨35,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨36,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨37,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨38,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨39,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨40,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨41,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨42,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨43,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨44,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨45,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨46,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨47,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨48,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨49,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨50,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨51,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12489) (by norm_num)
        (q := 1 - (cell12489 ⟨52,by decide⟩).lower)
        (by norm_num [cell12489]) (by norm_num [cell12489])
      exact ⟨E.1,E.2.trans (by norm_num [cell12489])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12489

/-! Source-cell containment and simple scalar guards at 12489. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12489)
open BstLean.Part268 (cell12489)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12489 ⟨10,by decide⟩).lower ∧ (cell12489 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12489 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12489 ⟨11,by decide⟩).lower ∧ (cell12489 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12489 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12489 ⟨12,by decide⟩).lower ∧ (cell12489 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12489 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12489 ⟨13,by decide⟩).lower ∧ (cell12489 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12489 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12489 ⟨14,by decide⟩).lower ∧ (cell12489 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12489 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12489 ⟨15,by decide⟩).lower ∧ (cell12489 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12489 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12489 ⟨16,by decide⟩).lower ∧ (cell12489 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12489 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12489 ⟨17,by decide⟩).lower ∧ (cell12489 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12489 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12489 ⟨18,by decide⟩).lower ∧ (cell12489 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12489 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12489 ⟨19,by decide⟩).lower ∧ (cell12489 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12489 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12489 ⟨20,by decide⟩).lower ∧ (cell12489 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12489 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12489 ⟨21,by decide⟩).lower ∧ (cell12489 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12489 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12489 ⟨22,by decide⟩).lower ∧ (cell12489 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12489 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12489 ⟨23,by decide⟩).lower ∧ (cell12489 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12489 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12489 ⟨24,by decide⟩).lower ∧ (cell12489 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12489 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12489 ⟨25,by decide⟩).lower ∧ (cell12489 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12489 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12489 ⟨26,by decide⟩).lower ∧ (cell12489 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12489 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12489 ⟨27,by decide⟩).lower ∧ (cell12489 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12489 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12489 ⟨28,by decide⟩).lower ∧ (cell12489 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12489 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12489 ⟨29,by decide⟩).lower ∧ (cell12489 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12489 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12489 ⟨30,by decide⟩).lower ∧ (cell12489 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12489 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12489 ⟨31,by decide⟩).lower ∧ (cell12489 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12489 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12489 ⟨32,by decide⟩).lower ∧ (cell12489 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12489 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12489 ⟨33,by decide⟩).lower ∧ (cell12489 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12489 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12489 ⟨34,by decide⟩).lower ∧ (cell12489 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12489 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12489 ⟨35,by decide⟩).lower ∧ (cell12489 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12489 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12489 ⟨36,by decide⟩).lower ∧ (cell12489 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12489 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12489 ⟨37,by decide⟩).lower ∧ (cell12489 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12489 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12489 ⟨38,by decide⟩).lower ∧ (cell12489 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12489 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12489 ⟨39,by decide⟩).lower ∧ (cell12489 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12489 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12489 ⟨40,by decide⟩).lower ∧ (cell12489 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12489 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12489 ⟨41,by decide⟩).lower ∧ (cell12489 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12489 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12489 ⟨42,by decide⟩).lower ∧ (cell12489 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12489 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12489 ⟨43,by decide⟩).lower ∧ (cell12489 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12489 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12489 ⟨44,by decide⟩).lower ∧ (cell12489 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12489 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12489 ⟨45,by decide⟩).lower ∧ (cell12489 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12489 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12489 ⟨46,by decide⟩).lower ∧ (cell12489 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12489 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12489 ⟨47,by decide⟩).lower ∧ (cell12489 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12489 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12489 ⟨48,by decide⟩).lower ∧ (cell12489 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12489 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12489 ⟨49,by decide⟩).lower ∧ (cell12489 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12489 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12489 ⟨50,by decide⟩).lower ∧ (cell12489 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12489 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12489 ⟨51,by decide⟩).lower ∧ (cell12489 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12489 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12489 ⟨52,by decide⟩).lower ∧ (cell12489 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12489 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12489 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12489 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12489,cell12489,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12489 i).lower ∧
    (cell12489 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12489 i).upper ≤ (0.532 : ℝ) ∧
    (cell12489 i).centre ≤ (0.1 : ℝ) ∧ (cell12489 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12489 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12489 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12489

/-! The local source numeric instances at 12489 have no network premises. -/
namespace BstLean.Part269.N12489
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12489)
open BstLean.Part268 (cell12489)

noncomputable def sourceNumerics12489 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12489 (cell12489 i)
      scalarRow12489.M scalarRow12489.H scalarRow12489.xi := by
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
    energy_allowance := scalarRow12489.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12489]
    centre_nonneg := (scalarRow12489.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12489])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12489
/-! Actual 12490 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12490 ≤ (1.036111663273 : ℝ) := by
  have hr : (111.758668567588 : ℝ) ≤ √(12490 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.758668567588 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12490 12490 (11 / 1000) ≤
    (0.008553135995 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12490) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.758668567588 : ℝ) ≤ √(12490 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12490)
  have hdiv : K / √(12490 : ℝ) ≤ K / 111.758668567588 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.758668567588 ≤ (0.008553135995 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12490.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12490 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12490 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12490 := gPlus_lower 12490
end BstLean.Part269.N12490

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12490
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036111663272 : ℝ) ≤ wn 12490 := by
  have hn : √(12490 : ℝ) ≤ 111.758668567589 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12490 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.758668567589 ≤ 2 / √(12490 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256190638 : ℝ) ≤ rhoBar 12490 BstLean.Part154.csC ∧
    rhoBar 12490 BstLean.Part154.csC ≤ 0.000256191035 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036111663272 : ℝ) / (1.295212 * 12490) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036111663273 : ℝ) / (1.29521 * 12490) := by gcongr
      _ ≤ (0.000256191035 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12490 BstLean.Part154.csC) ≤ 0.001024829774 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12490 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) ≤ 0.000195680597 ∧
    cc1 (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) ≤ 0.000124512831 ∧
    cc2 (rhoBar 12490 BstLean.Part154.csC) ≤ 0.000072280613 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12490 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12490 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12490 BstLean.Part154.csC * nuR (rhoBar 12490 BstLean.Part154.csC)) ≤ 0.000512398479 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256191035 : ℝ) * 0.001024829774 := by gcongr
      _ ≤ (0.000512398479 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12490 BstLean.Part154.csC) * nuR (rhoBar 12490 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024829774 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12490 BstLean.Part154.csC) * rhoBar 12490 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256191035 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256191035 / 2 + 0.399 * 0.001024829774 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195680597 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512398479 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124512831 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256191035 / 1.414213562 := by gcongr
      _ ≤ (0.000072280613 : ℝ) := by norm_num

end BstLean.Part269.N12490

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12490
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) ≤ 1.65360E-7 := by
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12490 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12490 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12490 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195680597 : ℝ) ^ 2 + 0.000124512831 ^ 2 + 3 * 0.000072280613 ^ 2 +
        2 * 0.797885 * 0.000195680597 * 0.000124512831 + 2 * 0.000195680597 * 0.000072280613 +
        4 * 0.797885 * 0.000124512831 * 0.000072280613 := by gcongr
    _ ≤ (1.65360E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12490 BstLean.Part154.csC Θ ≤ 0.002675061447 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12490 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12490 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12490 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036111663273 * 1.65360E-7 / (0.000256190638 : ℝ) := by gcongr
    _ ≤ 0.002675061447 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12490 BstLean.Part154.csC Θ ≤ 0.002968990933 + 0.000675943966 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12490 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12490 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036111663273 : ℝ) * ((2 * Θ * 0.000256191035 +
        (6863 / 10000) * 0.000256191035 * 12490 * 0.001024829774) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002968990933 + 0.000675943966 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12490 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12490 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12490 0.011 Θ ∧ gammaRatio 12490 0.011 Θ ≤ 0.000088071853 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12490 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036111663273 : ℝ) * 0.525 / ((1 - 0.011) * 12490) := by gcongr
      _ ≤ (0.000088071853 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12490 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12490 0.011 Θ) :=
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
    badAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12490 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12490 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12490 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12490 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12490 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12490 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12490 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12490 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12490 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12490 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036111663273 : ℝ) * 12490 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003786330095 + 0.003351005413 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12490

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12490
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12490 BstLean.Part154.csC) (piBar (rhoBar 12490 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12490 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12490 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12490 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12490 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12490 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12490 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12490 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12490 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12490 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12490 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052928499127 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12490) ≤ 0.010685860850 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12490 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036111663273)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010685860850 + 2 * 0.737676 / 12490) := by gcongr
    _ ≤ (0.052928499127 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12490 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12490

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12490
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493911793 : ℝ) ≤ plow 12490 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12490) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052207937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404407260) : eMP 12490 0.011 xi bn ≤ 0.001208779372 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12490 : ℝ) * (1 - 0.011))) ≤ 0.000597643401 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404407260 / (12490 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597643401 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597643401 : ℝ) + 3.141593 * 0.053052207937 / (12490 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208779372 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052207937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404407260) : PiBarMP 12490 12 0.011 xi bn ≤ 0.162615116008 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12490 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037475422080 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.142296179267 : ℝ) ≤ √((12490 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.758668567588 : ℝ) ≤ √(12490 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12490) ≤ 0.124665123890 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037475422080 + 0.053052207937 * 1.772454 / (2 * (111.142296179267 : ℝ))) * (1 + 0.001208779372) +
        8 / (12490 * 111.758668567588) + 0.124665123890 := by gcongr
    _ ≤ (0.162615116008 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052207937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404407260) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283259148276) :
    parallelOracle 12490 0.011 xi bn cd ≤ 0.163623240664 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12490 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12490 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493911793 : ℝ) ≤ plow 12490 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.758668567588 : ℝ) ≤ √(12490 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283259148276 : ℝ) / (2 * 0.560493911793 * 111.758668567588)) * 0.162615116008 +
        0.283259148276 ^ 2 / (2 * 0.560493911793 * 111.758668567588) := by gcongr
    _ ≤ (0.163623240664 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053052207937) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404407260)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283259148276) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12490 12490 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493911793 : ℝ) ≤ plow 12490 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.758668567588 : ℝ) ≤ √(12490 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12490 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12490 Θ 1.22 ≤ 0.011865750702 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.758668567588 := by gcongr <;> linarith
      _ ≤ (0.011865750702 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12490 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12490 12490 0.011 ≤ 0.008553135995 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12490 12490 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12490 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12490 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12490 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12490 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163623240664 + 0.011865750702 + (0.008553135995 : ℝ) *
        (1 + 2 * (0.283259148276 + 0.011865750702) / (0.560493911793 * 111.758668567588))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12490]

end BstLean.Part269.N12490

/-! The original eight local profiles supply actual 12490 moment certificates. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12490 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053052207937 ∧
    0 ≤ bN 12490 BstLean.Part154.csC (groupTheta g) ∧ bN 12490 BstLean.Part154.csC (groupTheta g) ≤ 0.001404407260 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12490 12490 0.011
      (momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12490 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12490 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12490 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230330649149 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12490 0.011
      (momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12490 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12490
/-! The actual computed-centre upper energy formula at 12490. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12490

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12490)
open BstLean.Part268 (cell12490)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086128395209
  | 2 => 0.087083472775
  | 3 => 0.088038584052
  | 4 => 0.088995576094
  | 5 => 0.089956667574
  | 6 => 0.090924501931
  | 7 => 0.091902205151
  | 8 => 0.092893448155
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12490 12490 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12490 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12490

/-! Actual upper energy certificates on all 43 source endpoints at 12490. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12490)
open BstLean.Part268 (cell12490)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12490 (gMinus 12490) (1 - (cell12490 i).lower) ≤ 1 ∧
    energyUpper 12490 (gMinus 12490) (BstLean.Part211.gPlus 12490)
      (finiteEnergy 12490 12490 0.011) (1 - (cell12490 i).lower) ≤
      (cell12490 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨10,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨11,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨12,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨13,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨14,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨15,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨16,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨17,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨18,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨19,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨20,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨21,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨22,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨23,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨24,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨25,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨26,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨27,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨28,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨29,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨30,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨31,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨32,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨33,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨34,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨35,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨36,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨37,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨38,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨39,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨40,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨41,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨42,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨43,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨44,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨45,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨46,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨47,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨48,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨49,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨50,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨51,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12490) (by norm_num)
        (q := 1 - (cell12490 ⟨52,by decide⟩).lower)
        (by norm_num [cell12490]) (by norm_num [cell12490])
      exact ⟨E.1,E.2.trans (by norm_num [cell12490])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12490

/-! Source-cell containment and simple scalar guards at 12490. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12490)
open BstLean.Part268 (cell12490)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12490 ⟨10,by decide⟩).lower ∧ (cell12490 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12490 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12490 ⟨11,by decide⟩).lower ∧ (cell12490 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12490 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12490 ⟨12,by decide⟩).lower ∧ (cell12490 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12490 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12490 ⟨13,by decide⟩).lower ∧ (cell12490 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12490 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12490 ⟨14,by decide⟩).lower ∧ (cell12490 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12490 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12490 ⟨15,by decide⟩).lower ∧ (cell12490 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12490 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12490 ⟨16,by decide⟩).lower ∧ (cell12490 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12490 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12490 ⟨17,by decide⟩).lower ∧ (cell12490 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12490 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12490 ⟨18,by decide⟩).lower ∧ (cell12490 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12490 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12490 ⟨19,by decide⟩).lower ∧ (cell12490 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12490 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12490 ⟨20,by decide⟩).lower ∧ (cell12490 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12490 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12490 ⟨21,by decide⟩).lower ∧ (cell12490 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12490 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12490 ⟨22,by decide⟩).lower ∧ (cell12490 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12490 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12490 ⟨23,by decide⟩).lower ∧ (cell12490 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12490 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12490 ⟨24,by decide⟩).lower ∧ (cell12490 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12490 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12490 ⟨25,by decide⟩).lower ∧ (cell12490 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12490 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12490 ⟨26,by decide⟩).lower ∧ (cell12490 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12490 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12490 ⟨27,by decide⟩).lower ∧ (cell12490 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12490 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12490 ⟨28,by decide⟩).lower ∧ (cell12490 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12490 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12490 ⟨29,by decide⟩).lower ∧ (cell12490 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12490 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12490 ⟨30,by decide⟩).lower ∧ (cell12490 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12490 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12490 ⟨31,by decide⟩).lower ∧ (cell12490 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12490 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12490 ⟨32,by decide⟩).lower ∧ (cell12490 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12490 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12490 ⟨33,by decide⟩).lower ∧ (cell12490 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12490 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12490 ⟨34,by decide⟩).lower ∧ (cell12490 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12490 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12490 ⟨35,by decide⟩).lower ∧ (cell12490 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12490 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12490 ⟨36,by decide⟩).lower ∧ (cell12490 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12490 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12490 ⟨37,by decide⟩).lower ∧ (cell12490 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12490 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12490 ⟨38,by decide⟩).lower ∧ (cell12490 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12490 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12490 ⟨39,by decide⟩).lower ∧ (cell12490 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12490 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12490 ⟨40,by decide⟩).lower ∧ (cell12490 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12490 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12490 ⟨41,by decide⟩).lower ∧ (cell12490 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12490 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12490 ⟨42,by decide⟩).lower ∧ (cell12490 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12490 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12490 ⟨43,by decide⟩).lower ∧ (cell12490 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12490 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12490 ⟨44,by decide⟩).lower ∧ (cell12490 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12490 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12490 ⟨45,by decide⟩).lower ∧ (cell12490 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12490 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12490 ⟨46,by decide⟩).lower ∧ (cell12490 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12490 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12490 ⟨47,by decide⟩).lower ∧ (cell12490 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12490 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12490 ⟨48,by decide⟩).lower ∧ (cell12490 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12490 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12490 ⟨49,by decide⟩).lower ∧ (cell12490 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12490 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12490 ⟨50,by decide⟩).lower ∧ (cell12490 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12490 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12490 ⟨51,by decide⟩).lower ∧ (cell12490 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12490 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12490 ⟨52,by decide⟩).lower ∧ (cell12490 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12490 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12490 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12490 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12490,cell12490,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12490 i).lower ∧
    (cell12490 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12490 i).upper ≤ (0.532 : ℝ) ∧
    (cell12490 i).centre ≤ (0.1 : ℝ) ∧ (cell12490 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12490 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12490 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12490

/-! The local source numeric instances at 12490 have no network premises. -/
namespace BstLean.Part269.N12490
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12490)
open BstLean.Part268 (cell12490)

noncomputable def sourceNumerics12490 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12490 (cell12490 i)
      scalarRow12490.M scalarRow12490.H scalarRow12490.xi := by
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
    energy_allowance := scalarRow12490.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12490]
    centre_nonneg := (scalarRow12490.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12490])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12490
/-! Actual 12491 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12491 ≤ (1.036110204917 : ℝ) := by
  have hr : (111.763142403924 : ℝ) ≤ √(12491 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.763142403924 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12491 12491 (11 / 1000) ≤
    (0.008552793614 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12491) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.763142403924 : ℝ) ≤ √(12491 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12491)
  have hdiv : K / √(12491 : ℝ) ≤ K / 111.763142403924 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.763142403924 ≤ (0.008552793614 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12491.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12491 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12491 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12491 := gPlus_lower 12491
end BstLean.Part269.N12491

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12491
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036110204916 : ℝ) ≤ wn 12491 := by
  have hn : √(12491 : ℝ) ≤ 111.763142403925 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12491 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.763142403925 ≤ 2 / √(12491 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256169767 : ℝ) ≤ rhoBar 12491 BstLean.Part154.csC ∧
    rhoBar 12491 BstLean.Part154.csC ≤ 0.000256170164 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036110204916 : ℝ) / (1.295212 * 12491) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036110204917 : ℝ) / (1.29521 * 12491) := by gcongr
      _ ≤ (0.000256170164 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12491 BstLean.Part154.csC) ≤ 0.001024746280 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12491 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) ≤ 0.000195664654 ∧
    cc1 (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) ≤ 0.000124502687 ∧
    cc2 (rhoBar 12491 BstLean.Part154.csC) ≤ 0.000072274725 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12491 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12491 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12491 BstLean.Part154.csC * nuR (rhoBar 12491 BstLean.Part154.csC)) ≤ 0.000512356734 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256170164 : ℝ) * 0.001024746280 := by gcongr
      _ ≤ (0.000512356734 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12491 BstLean.Part154.csC) * nuR (rhoBar 12491 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024746280 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12491 BstLean.Part154.csC) * rhoBar 12491 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256170164 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256170164 / 2 + 0.399 * 0.001024746280 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195664654 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512356734 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124502687 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256170164 / 1.414213562 := by gcongr
      _ ≤ (0.000072274725 : ℝ) := by norm_num

end BstLean.Part269.N12491

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12491
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) ≤ 1.65333E-7 := by
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12491 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12491 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12491 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195664654 : ℝ) ^ 2 + 0.000124502687 ^ 2 + 3 * 0.000072274725 ^ 2 +
        2 * 0.797885 * 0.000195664654 * 0.000124502687 + 2 * 0.000195664654 * 0.000072274725 +
        4 * 0.797885 * 0.000124502687 * 0.000072274725 := by gcongr
    _ ≤ (1.65333E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12491 BstLean.Part154.csC Θ ≤ 0.002674838808 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12491 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12491 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12491 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036110204917 * 1.65333E-7 / (0.000256169767 : ℝ) := by gcongr
    _ ≤ 0.002674838808 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12491 BstLean.Part154.csC Θ ≤ 0.002968740685 + 0.000675887948 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12491 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12491 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036110204917 : ℝ) * ((2 * Θ * 0.000256170164 +
        (6863 / 10000) * 0.000256170164 * 12491 * 0.001024746280) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002968740685 + 0.000675887948 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12491 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12491 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12491 0.011 Θ ∧ gammaRatio 12491 0.011 Θ ≤ 0.000088064678 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12491 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036110204917 : ℝ) * 0.525 / ((1 - 0.011) * 12491) := by gcongr
      _ ≤ (0.000088064678 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12491 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12491 0.011 Θ) :=
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
    badAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12491 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12491 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12491 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12491 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12491 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12491 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12491 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12491 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12491 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12491 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036110204917 : ℝ) * 12491 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003786079847 + 0.003350726756 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12491

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12491
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12491 BstLean.Part154.csC) (piBar (rhoBar 12491 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12491 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12491 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12491 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12491 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12491 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12491 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12491 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12491 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12491 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12491 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052926357256 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12491) ≤ 0.010685433099 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12491 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036110204917)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010685433099 + 2 * 0.737676 / 12491) := by gcongr
    _ ≤ (0.052926357256 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12491 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12491

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12491
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493958546 : ℝ) ≤ plow 12491 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12491) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051811394)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404290375) : eMP 12491 0.011 xi bn ≤ 0.001208680605 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12491 : ℝ) * (1 - 0.011))) ≤ 0.000597594608 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404290375 / (12491 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597594608 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597594608 : ℝ) + 3.141593 * 0.053051811394 / (12491 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208680605 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051811394)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404290375) : PiBarMP 12491 12 0.011 xi bn ≤ 0.162608539753 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12491 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037473862558 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.146745341462 : ℝ) ≤ √((12491 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.763142403924 : ℝ) ≤ √(12491 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12491) ≤ 0.124660133593 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037473862558 + 0.053051811394 * 1.772454 / (2 * (111.146745341462 : ℝ))) * (1 + 0.001208680605) +
        8 / (12491 * 111.763142403924) + 0.124660133593 := by gcongr
    _ ≤ (0.162608539753 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051811394)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404290375) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283256145591) :
    parallelOracle 12491 0.011 xi bn cd ≤ 0.163616591627 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12491 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12491 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493958546 : ℝ) ≤ plow 12491 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.763142403924 : ℝ) ≤ √(12491 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283256145591 : ℝ) / (2 * 0.560493958546 * 111.763142403924)) * 0.162608539753 +
        0.283256145591 ^ 2 / (2 * 0.560493958546 * 111.763142403924) := by gcongr
    _ ≤ (0.163616591627 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051811394) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404290375)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283256145591) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12491 12491 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493958546 : ℝ) ≤ plow 12491 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.763142403924 : ℝ) ≤ √(12491 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12491 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12491 Θ 1.22 ≤ 0.011865275721 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.763142403924 := by gcongr <;> linarith
      _ ≤ (0.011865275721 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12491 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12491 12491 0.011 ≤ 0.008552793614 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12491 12491 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12491 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12491 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12491 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12491 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163616591627 + 0.011865275721 + (0.008552793614 : ℝ) *
        (1 + 2 * (0.283256145591 + 0.011865275721) / (0.560493958546 * 111.763142403924))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12491]

end BstLean.Part269.N12491

/-! The original eight local profiles supply actual 12491 moment certificates. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12491 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053051811394 ∧
    0 ≤ bN 12491 BstLean.Part154.csC (groupTheta g) ∧ bN 12491 BstLean.Part154.csC (groupTheta g) ≤ 0.001404290375 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12491 12491 0.011
      (momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12491 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12491 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12491 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230329788335 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12491 0.011
      (momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12491 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12491
/-! The actual computed-centre upper energy formula at 12491. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12491

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12491)
open BstLean.Part268 (cell12491)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086125225402
  | 2 => 0.087080238674
  | 3 => 0.088035275328
  | 4 => 0.088992180115
  | 5 => 0.089953169009
  | 6 => 0.090920882315
  | 7 => 0.091898442390
  | 8 => 0.092889515991
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12491 12491 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12491 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12491

/-! Actual upper energy certificates on all 43 source endpoints at 12491. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12491)
open BstLean.Part268 (cell12491)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12491 (gMinus 12491) (1 - (cell12491 i).lower) ≤ 1 ∧
    energyUpper 12491 (gMinus 12491) (BstLean.Part211.gPlus 12491)
      (finiteEnergy 12491 12491 0.011) (1 - (cell12491 i).lower) ≤
      (cell12491 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨10,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨11,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨12,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨13,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨14,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨15,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨16,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨17,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨18,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨19,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨20,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨21,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨22,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨23,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨24,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨25,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨26,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨27,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨28,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨29,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨30,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨31,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨32,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨33,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨34,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨35,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨36,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨37,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨38,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨39,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨40,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨41,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨42,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨43,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨44,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨45,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨46,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨47,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨48,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨49,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨50,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨51,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12491) (by norm_num)
        (q := 1 - (cell12491 ⟨52,by decide⟩).lower)
        (by norm_num [cell12491]) (by norm_num [cell12491])
      exact ⟨E.1,E.2.trans (by norm_num [cell12491])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12491

/-! Source-cell containment and simple scalar guards at 12491. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12491)
open BstLean.Part268 (cell12491)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12491 ⟨10,by decide⟩).lower ∧ (cell12491 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12491 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12491 ⟨11,by decide⟩).lower ∧ (cell12491 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12491 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12491 ⟨12,by decide⟩).lower ∧ (cell12491 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12491 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12491 ⟨13,by decide⟩).lower ∧ (cell12491 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12491 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12491 ⟨14,by decide⟩).lower ∧ (cell12491 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12491 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12491 ⟨15,by decide⟩).lower ∧ (cell12491 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12491 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12491 ⟨16,by decide⟩).lower ∧ (cell12491 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12491 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12491 ⟨17,by decide⟩).lower ∧ (cell12491 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12491 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12491 ⟨18,by decide⟩).lower ∧ (cell12491 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12491 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12491 ⟨19,by decide⟩).lower ∧ (cell12491 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12491 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12491 ⟨20,by decide⟩).lower ∧ (cell12491 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12491 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12491 ⟨21,by decide⟩).lower ∧ (cell12491 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12491 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12491 ⟨22,by decide⟩).lower ∧ (cell12491 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12491 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12491 ⟨23,by decide⟩).lower ∧ (cell12491 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12491 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12491 ⟨24,by decide⟩).lower ∧ (cell12491 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12491 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12491 ⟨25,by decide⟩).lower ∧ (cell12491 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12491 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12491 ⟨26,by decide⟩).lower ∧ (cell12491 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12491 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12491 ⟨27,by decide⟩).lower ∧ (cell12491 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12491 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12491 ⟨28,by decide⟩).lower ∧ (cell12491 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12491 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12491 ⟨29,by decide⟩).lower ∧ (cell12491 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12491 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12491 ⟨30,by decide⟩).lower ∧ (cell12491 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12491 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12491 ⟨31,by decide⟩).lower ∧ (cell12491 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12491 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12491 ⟨32,by decide⟩).lower ∧ (cell12491 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12491 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12491 ⟨33,by decide⟩).lower ∧ (cell12491 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12491 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12491 ⟨34,by decide⟩).lower ∧ (cell12491 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12491 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12491 ⟨35,by decide⟩).lower ∧ (cell12491 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12491 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12491 ⟨36,by decide⟩).lower ∧ (cell12491 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12491 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12491 ⟨37,by decide⟩).lower ∧ (cell12491 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12491 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12491 ⟨38,by decide⟩).lower ∧ (cell12491 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12491 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12491 ⟨39,by decide⟩).lower ∧ (cell12491 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12491 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12491 ⟨40,by decide⟩).lower ∧ (cell12491 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12491 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12491 ⟨41,by decide⟩).lower ∧ (cell12491 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12491 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12491 ⟨42,by decide⟩).lower ∧ (cell12491 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12491 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12491 ⟨43,by decide⟩).lower ∧ (cell12491 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12491 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12491 ⟨44,by decide⟩).lower ∧ (cell12491 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12491 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12491 ⟨45,by decide⟩).lower ∧ (cell12491 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12491 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12491 ⟨46,by decide⟩).lower ∧ (cell12491 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12491 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12491 ⟨47,by decide⟩).lower ∧ (cell12491 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12491 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12491 ⟨48,by decide⟩).lower ∧ (cell12491 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12491 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12491 ⟨49,by decide⟩).lower ∧ (cell12491 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12491 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12491 ⟨50,by decide⟩).lower ∧ (cell12491 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12491 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12491 ⟨51,by decide⟩).lower ∧ (cell12491 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12491 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12491 ⟨52,by decide⟩).lower ∧ (cell12491 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12491 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12491 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12491 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12491,cell12491,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12491 i).lower ∧
    (cell12491 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12491 i).upper ≤ (0.532 : ℝ) ∧
    (cell12491 i).centre ≤ (0.1 : ℝ) ∧ (cell12491 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12491 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12491 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12491

/-! The local source numeric instances at 12491 have no network premises. -/
namespace BstLean.Part269.N12491
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12491)
open BstLean.Part268 (cell12491)

noncomputable def sourceNumerics12491 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12491 (cell12491 i)
      scalarRow12491.M scalarRow12491.H scalarRow12491.xi := by
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
    energy_allowance := scalarRow12491.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12491]
    centre_nonneg := (scalarRow12491.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12491])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12491
/-! Actual 12492 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12492 ≤ (1.036108746738 : ℝ) := by
  have hr : (111.767616061182 : ℝ) ≤ √(12492 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.767616061182 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12492 12492 (11 / 1000) ≤
    (0.008552451273 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12492) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.767616061182 : ℝ) ≤ √(12492 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12492)
  have hdiv : K / √(12492 : ℝ) ≤ K / 111.767616061182 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.767616061182 ≤ (0.008552451273 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12492.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12492 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12492 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12492 := gPlus_lower 12492
end BstLean.Part269.N12492

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12492
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036108746737 : ℝ) ≤ wn 12492 := by
  have hn : √(12492 : ℝ) ≤ 111.767616061183 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12492 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.767616061183 ≤ 2 / √(12492 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256148900 : ℝ) ≤ rhoBar 12492 BstLean.Part154.csC ∧
    rhoBar 12492 BstLean.Part154.csC ≤ 0.000256149297 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036108746737 : ℝ) / (1.295212 * 12492) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036108746738 : ℝ) / (1.29521 * 12492) := by gcongr
      _ ≤ (0.000256149297 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12492 BstLean.Part154.csC) ≤ 0.001024662801 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12492 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) ≤ 0.000195648715 ∧
    cc1 (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) ≤ 0.000124492545 ∧
    cc2 (rhoBar 12492 BstLean.Part154.csC) ≤ 0.000072268838 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12492 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12492 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12492 BstLean.Part154.csC * nuR (rhoBar 12492 BstLean.Part154.csC)) ≤ 0.000512314997 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256149297 : ℝ) * 0.001024662801 := by gcongr
      _ ≤ (0.000512314997 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12492 BstLean.Part154.csC) * nuR (rhoBar 12492 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024662801 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12492 BstLean.Part154.csC) * rhoBar 12492 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256149297 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256149297 / 2 + 0.399 * 0.001024662801 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195648715 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512314997 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124492545 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256149297 / 1.414213562 := by gcongr
      _ ≤ (0.000072268838 : ℝ) := by norm_num

end BstLean.Part269.N12492

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12492
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) ≤ 1.65306E-7 := by
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12492 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12492 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12492 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195648715 : ℝ) ^ 2 + 0.000124492545 ^ 2 + 3 * 0.000072268838 ^ 2 +
        2 * 0.797885 * 0.000195648715 * 0.000124492545 + 2 * 0.000195648715 * 0.000072268838 +
        4 * 0.797885 * 0.000124492545 * 0.000072268838 := by gcongr
    _ ≤ (1.65306E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12492 BstLean.Part154.csC Θ ≤ 0.002674616093 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12492 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12492 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12492 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036108746738 * 1.65306E-7 / (0.000256148900 : ℝ) := by gcongr
    _ ≤ 0.002674616093 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12492 BstLean.Part154.csC Θ ≤ 0.002968490489 + 0.000675831941 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12492 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12492 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036108746738 : ℝ) * ((2 * Θ * 0.000256149297 +
        (6863 / 10000) * 0.000256149297 * 12492 * 0.001024662801) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002968490489 + 0.000675831941 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12492 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12492 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12492 0.011 Θ ∧ gammaRatio 12492 0.011 Θ ≤ 0.000088057505 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12492 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036108746738 : ℝ) * 0.525 / ((1 - 0.011) * 12492) := by gcongr
      _ ≤ (0.000088057505 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12492 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12492 0.011 Θ) :=
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
    badAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12492 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12492 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12492 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12492 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12492 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12492 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12492 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12492 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12492 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12492 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036108746738 : ℝ) * 12492 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003785829651 + 0.003350448034 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12492

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12492
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12492 BstLean.Part154.csC) (piBar (rhoBar 12492 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12492 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12492 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12492 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12492 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12492 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12492 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12492 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12492 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12492 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12492 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052924215647 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12492) ≤ 0.010685005400 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12492 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036108746738)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010685005400 + 2 * 0.737676 / 12492) := by gcongr
    _ ≤ (0.052924215647 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12492 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12492

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12492
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494005291 : ℝ) ≤ plow 12492 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12492) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051414869)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404173449) : eMP 12492 0.011 xi bn ≤ 0.001208581828 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12492 : ℝ) * (1 - 0.011))) ≤ 0.000597545810 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404173449 / (12492 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597545810 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597545810 : ℝ) + 3.141593 * 0.053051414869 / (12492 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208581828 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051414869)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404173449) : PiBarMP 12492 12 0.011 xi bn ≤ 0.162601963486 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12492 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037472302425 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.151194325567 : ℝ) ≤ √((12492 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.767616061182 : ℝ) ≤ √(12492 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12492) ≤ 0.124655143894 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037472302425 + 0.053051414869 * 1.772454 / (2 * (111.151194325567 : ℝ))) * (1 + 0.001208581828) +
        8 / (12492 * 111.767616061182) + 0.124655143894 := by gcongr
    _ ≤ (0.162601963486 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051414869)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404173449) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283253143203) :
    parallelOracle 12492 0.011 xi bn cd ≤ 0.163609942587 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12492 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12492 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494005291 : ℝ) ≤ plow 12492 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.767616061182 : ℝ) ≤ √(12492 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283253143203 : ℝ) / (2 * 0.560494005291 * 111.767616061182)) * 0.162601963486 +
        0.283253143203 ^ 2 / (2 * 0.560494005291 * 111.767616061182) := by gcongr
    _ ≤ (0.163609942587 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051414869) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404173449)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283253143203) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12492 12492 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494005291 : ℝ) ≤ plow 12492 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.767616061182 : ℝ) ≤ √(12492 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12492 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12492 Θ 1.22 ≤ 0.011864800796 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.767616061182 := by gcongr <;> linarith
      _ ≤ (0.011864800796 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12492 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12492 12492 0.011 ≤ 0.008552451273 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12492 12492 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12492 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12492 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12492 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12492 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163609942587 + 0.011864800796 + (0.008552451273 : ℝ) *
        (1 + 2 * (0.283253143203 + 0.011864800796) / (0.560494005291 * 111.767616061182))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12492]

end BstLean.Part269.N12492

/-! The original eight local profiles supply actual 12492 moment certificates. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12492 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053051414869 ∧
    0 ≤ bN 12492 BstLean.Part154.csC (groupTheta g) ∧ bN 12492 BstLean.Part154.csC (groupTheta g) ≤ 0.001404173449 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12492 12492 0.011
      (momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12492 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12492 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12492 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230328927556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12492 0.011
      (momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12492 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12492
/-! The actual computed-centre upper energy formula at 12492. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12492

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12492)
open BstLean.Part268 (cell12492)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086122056943
  | 2 => 0.087077005979
  | 3 => 0.088031968081
  | 4 => 0.088988785701
  | 5 => 0.089949672119
  | 6 => 0.090917264504
  | 7 => 0.091894681592
  | 8 => 0.092885585980
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12492 12492 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12492 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12492

/-! Actual upper energy certificates on all 43 source endpoints at 12492. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12492)
open BstLean.Part268 (cell12492)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12492 (gMinus 12492) (1 - (cell12492 i).lower) ≤ 1 ∧
    energyUpper 12492 (gMinus 12492) (BstLean.Part211.gPlus 12492)
      (finiteEnergy 12492 12492 0.011) (1 - (cell12492 i).lower) ≤
      (cell12492 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨10,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨11,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨12,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨13,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨14,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨15,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨16,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨17,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨18,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨19,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨20,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨21,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨22,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨23,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨24,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨25,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨26,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨27,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨28,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨29,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨30,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨31,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨32,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨33,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨34,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨35,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨36,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨37,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨38,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨39,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨40,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨41,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨42,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨43,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨44,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨45,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨46,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨47,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨48,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨49,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨50,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨51,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12492) (by norm_num)
        (q := 1 - (cell12492 ⟨52,by decide⟩).lower)
        (by norm_num [cell12492]) (by norm_num [cell12492])
      exact ⟨E.1,E.2.trans (by norm_num [cell12492])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12492

/-! Source-cell containment and simple scalar guards at 12492. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12492)
open BstLean.Part268 (cell12492)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12492 ⟨10,by decide⟩).lower ∧ (cell12492 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12492 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12492 ⟨11,by decide⟩).lower ∧ (cell12492 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12492 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12492 ⟨12,by decide⟩).lower ∧ (cell12492 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12492 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12492 ⟨13,by decide⟩).lower ∧ (cell12492 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12492 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12492 ⟨14,by decide⟩).lower ∧ (cell12492 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12492 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12492 ⟨15,by decide⟩).lower ∧ (cell12492 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12492 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12492 ⟨16,by decide⟩).lower ∧ (cell12492 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12492 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12492 ⟨17,by decide⟩).lower ∧ (cell12492 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12492 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12492 ⟨18,by decide⟩).lower ∧ (cell12492 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12492 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12492 ⟨19,by decide⟩).lower ∧ (cell12492 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12492 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12492 ⟨20,by decide⟩).lower ∧ (cell12492 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12492 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12492 ⟨21,by decide⟩).lower ∧ (cell12492 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12492 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12492 ⟨22,by decide⟩).lower ∧ (cell12492 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12492 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12492 ⟨23,by decide⟩).lower ∧ (cell12492 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12492 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12492 ⟨24,by decide⟩).lower ∧ (cell12492 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12492 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12492 ⟨25,by decide⟩).lower ∧ (cell12492 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12492 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12492 ⟨26,by decide⟩).lower ∧ (cell12492 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12492 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12492 ⟨27,by decide⟩).lower ∧ (cell12492 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12492 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12492 ⟨28,by decide⟩).lower ∧ (cell12492 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12492 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12492 ⟨29,by decide⟩).lower ∧ (cell12492 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12492 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12492 ⟨30,by decide⟩).lower ∧ (cell12492 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12492 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12492 ⟨31,by decide⟩).lower ∧ (cell12492 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12492 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12492 ⟨32,by decide⟩).lower ∧ (cell12492 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12492 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12492 ⟨33,by decide⟩).lower ∧ (cell12492 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12492 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12492 ⟨34,by decide⟩).lower ∧ (cell12492 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12492 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12492 ⟨35,by decide⟩).lower ∧ (cell12492 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12492 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12492 ⟨36,by decide⟩).lower ∧ (cell12492 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12492 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12492 ⟨37,by decide⟩).lower ∧ (cell12492 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12492 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12492 ⟨38,by decide⟩).lower ∧ (cell12492 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12492 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12492 ⟨39,by decide⟩).lower ∧ (cell12492 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12492 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12492 ⟨40,by decide⟩).lower ∧ (cell12492 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12492 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12492 ⟨41,by decide⟩).lower ∧ (cell12492 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12492 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12492 ⟨42,by decide⟩).lower ∧ (cell12492 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12492 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12492 ⟨43,by decide⟩).lower ∧ (cell12492 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12492 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12492 ⟨44,by decide⟩).lower ∧ (cell12492 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12492 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12492 ⟨45,by decide⟩).lower ∧ (cell12492 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12492 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12492 ⟨46,by decide⟩).lower ∧ (cell12492 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12492 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12492 ⟨47,by decide⟩).lower ∧ (cell12492 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12492 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12492 ⟨48,by decide⟩).lower ∧ (cell12492 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12492 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12492 ⟨49,by decide⟩).lower ∧ (cell12492 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12492 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12492 ⟨50,by decide⟩).lower ∧ (cell12492 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12492 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12492 ⟨51,by decide⟩).lower ∧ (cell12492 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12492 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12492 ⟨52,by decide⟩).lower ∧ (cell12492 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12492 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12492 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12492 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12492,cell12492,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12492 i).lower ∧
    (cell12492 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12492 i).upper ≤ (0.532 : ℝ) ∧
    (cell12492 i).centre ≤ (0.1 : ℝ) ∧ (cell12492 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12492 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12492 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12492

/-! The local source numeric instances at 12492 have no network premises. -/
namespace BstLean.Part269.N12492
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12492)
open BstLean.Part268 (cell12492)

noncomputable def sourceNumerics12492 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12492 (cell12492 i)
      scalarRow12492.M scalarRow12492.H scalarRow12492.xi := by
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
    energy_allowance := scalarRow12492.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12492]
    centre_nonneg := (scalarRow12492.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12492])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12492
/-! Actual 12493 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12493 ≤ (1.036107288735 : ℝ) := by
  have hr : (111.772089539383 : ℝ) ≤ √(12493 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.772089539383 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12493 12493 (11 / 1000) ≤
    (0.008552108974 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12493) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.772089539383 : ℝ) ≤ √(12493 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12493)
  have hdiv : K / √(12493 : ℝ) ≤ K / 111.772089539383 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.772089539383 ≤ (0.008552108974 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12493.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12493 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12493 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12493 := gPlus_lower 12493
end BstLean.Part269.N12493

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12493
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036107288734 : ℝ) ≤ wn 12493 := by
  have hn : √(12493 : ℝ) ≤ 111.772089539384 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12493 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.772089539384 ≤ 2 / √(12493 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256128036 : ℝ) ≤ rhoBar 12493 BstLean.Part154.csC ∧
    rhoBar 12493 BstLean.Part154.csC ≤ 0.000256128433 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036107288734 : ℝ) / (1.295212 * 12493) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036107288735 : ℝ) / (1.29521 * 12493) := by gcongr
      _ ≤ (0.000256128433 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12493 BstLean.Part154.csC) ≤ 0.001024579334 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12493 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) ≤ 0.000195632778 ∧
    cc1 (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) ≤ 0.000124482404 ∧
    cc2 (rhoBar 12493 BstLean.Part154.csC) ≤ 0.000072262951 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12493 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12493 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12493 BstLean.Part154.csC * nuR (rhoBar 12493 BstLean.Part154.csC)) ≤ 0.000512273267 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256128433 : ℝ) * 0.001024579334 := by gcongr
      _ ≤ (0.000512273267 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12493 BstLean.Part154.csC) * nuR (rhoBar 12493 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024579334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12493 BstLean.Part154.csC) * rhoBar 12493 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256128433 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256128433 / 2 + 0.399 * 0.001024579334 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195632778 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512273267 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124482404 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256128433 / 1.414213562 := by gcongr
      _ ≤ (0.000072262951 : ℝ) := by norm_num

end BstLean.Part269.N12493

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12493
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) ≤ 1.65279E-7 := by
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12493 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12493 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12493 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195632778 : ℝ) ^ 2 + 0.000124482404 ^ 2 + 3 * 0.000072262951 ^ 2 +
        2 * 0.797885 * 0.000195632778 * 0.000124482404 + 2 * 0.000195632778 * 0.000072262951 +
        4 * 0.797885 * 0.000124482404 * 0.000072262951 := by gcongr
    _ ≤ (1.65279E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12493 BstLean.Part154.csC Θ ≤ 0.002674393312 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12493 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12493 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12493 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036107288735 * 1.65279E-7 / (0.000256128036 : ℝ) := by gcongr
    _ ≤ 0.002674393312 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12493 BstLean.Part154.csC Θ ≤ 0.002968240326 + 0.000675775942 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12493 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12493 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036107288735 : ℝ) * ((2 * Θ * 0.000256128433 +
        (6863 / 10000) * 0.000256128433 * 12493 * 0.001024579334) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002968240326 + 0.000675775942 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12493 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12493 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12493 0.011 Θ ∧ gammaRatio 12493 0.011 Θ ≤ 0.000088050332 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12493 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036107288735 : ℝ) * 0.525 / ((1 - 0.011) * 12493) := by gcongr
      _ ≤ (0.000088050332 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12493 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12493 0.011 Θ) :=
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
    badAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12493 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12493 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12493 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12493 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12493 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12493 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12493 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12493 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12493 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12493 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036107288735 : ℝ) * 12493 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003785579488 + 0.003350169254 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12493

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12493
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12493 BstLean.Part154.csC) (piBar (rhoBar 12493 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12493 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12493 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12493 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12493 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12493 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12493 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12493 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12493 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12493 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12493 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052922074290 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12493) ≤ 0.010684577751 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12493 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036107288735)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010684577751 + 2 * 0.737676 / 12493) := by gcongr
    _ ≤ (0.052922074290 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12493 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12493

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12493
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494052029 : ℝ) ≤ plow 12493 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12493) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051018347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404056489) : eMP 12493 0.011 xi bn ≤ 0.001208483045 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12493 : ℝ) * (1 - 0.011))) ≤ 0.000597497009 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404056489 / (12493 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597497009 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597497009 : ℝ) + 3.141593 * 0.053051018347 / (12493 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208483045 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051018347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404056489) : PiBarMP 12493 12 0.011 xi bn ≤ 0.162595387303 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12493 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037470741773 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.155643131601 : ℝ) ≤ √((12493 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.772089539383 : ℝ) ≤ √(12493 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12493) ≤ 0.124650154795 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037470741773 + 0.053051018347 * 1.772454 / (2 * (111.155643131601 : ℝ))) * (1 + 0.001208483045) +
        8 / (12493 * 111.772089539383) + 0.124650154795 := by gcongr
    _ ≤ (0.162595387303 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051018347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404056489) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283250141071) :
    parallelOracle 12493 0.011 xi bn cd ≤ 0.163603293642 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12493 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12493 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494052029 : ℝ) ≤ plow 12493 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.772089539383 : ℝ) ≤ √(12493 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283250141071 : ℝ) / (2 * 0.560494052029 * 111.772089539383)) * 0.162595387303 +
        0.283250141071 ^ 2 / (2 * 0.560494052029 * 111.772089539383) := by gcongr
    _ ≤ (0.163603293642 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053051018347) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404056489)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283250141071) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12493 12493 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494052029 : ℝ) ≤ plow 12493 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.772089539383 : ℝ) ≤ √(12493 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12493 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12493 Θ 1.22 ≤ 0.011864325929 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.772089539383 := by gcongr <;> linarith
      _ ≤ (0.011864325929 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12493 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12493 12493 0.011 ≤ 0.008552108974 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12493 12493 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12493 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12493 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12493 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12493 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163603293642 + 0.011864325929 + (0.008552108974 : ℝ) *
        (1 + 2 * (0.283250141071 + 0.011864325929) / (0.560494052029 * 111.772089539383))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12493]

end BstLean.Part269.N12493

/-! The original eight local profiles supply actual 12493 moment certificates. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12493 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053051018347 ∧
    0 ≤ bN 12493 BstLean.Part154.csC (groupTheta g) ∧ bN 12493 BstLean.Part154.csC (groupTheta g) ≤ 0.001404056489 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12493 12493 0.011
      (momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12493 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12493 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12493 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230328066781 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12493 0.011
      (momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12493 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12493
/-! The actual computed-centre upper energy formula at 12493. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12493

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12493)
open BstLean.Part268 (cell12493)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086118889830
  | 2 => 0.087073774688
  | 3 => 0.088028662311
  | 4 => 0.088985392853
  | 5 => 0.089946176901
  | 6 => 0.090913648496
  | 7 => 0.091890922755
  | 8 => 0.092881658118
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12493 12493 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12493 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12493

/-! Actual upper energy certificates on all 43 source endpoints at 12493. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12493)
open BstLean.Part268 (cell12493)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12493 (gMinus 12493) (1 - (cell12493 i).lower) ≤ 1 ∧
    energyUpper 12493 (gMinus 12493) (BstLean.Part211.gPlus 12493)
      (finiteEnergy 12493 12493 0.011) (1 - (cell12493 i).lower) ≤
      (cell12493 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨10,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨11,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨12,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨13,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨14,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨15,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨16,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨17,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨18,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨19,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨20,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨21,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨22,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨23,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨24,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨25,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨26,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨27,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨28,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨29,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨30,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨31,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨32,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨33,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨34,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨35,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨36,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨37,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨38,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨39,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨40,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨41,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨42,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨43,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨44,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨45,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨46,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨47,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨48,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨49,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨50,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨51,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12493) (by norm_num)
        (q := 1 - (cell12493 ⟨52,by decide⟩).lower)
        (by norm_num [cell12493]) (by norm_num [cell12493])
      exact ⟨E.1,E.2.trans (by norm_num [cell12493])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12493

/-! Source-cell containment and simple scalar guards at 12493. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12493)
open BstLean.Part268 (cell12493)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12493 ⟨10,by decide⟩).lower ∧ (cell12493 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12493 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12493 ⟨11,by decide⟩).lower ∧ (cell12493 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12493 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12493 ⟨12,by decide⟩).lower ∧ (cell12493 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12493 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12493 ⟨13,by decide⟩).lower ∧ (cell12493 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12493 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12493 ⟨14,by decide⟩).lower ∧ (cell12493 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12493 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12493 ⟨15,by decide⟩).lower ∧ (cell12493 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12493 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12493 ⟨16,by decide⟩).lower ∧ (cell12493 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12493 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12493 ⟨17,by decide⟩).lower ∧ (cell12493 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12493 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12493 ⟨18,by decide⟩).lower ∧ (cell12493 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12493 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12493 ⟨19,by decide⟩).lower ∧ (cell12493 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12493 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12493 ⟨20,by decide⟩).lower ∧ (cell12493 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12493 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12493 ⟨21,by decide⟩).lower ∧ (cell12493 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12493 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12493 ⟨22,by decide⟩).lower ∧ (cell12493 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12493 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12493 ⟨23,by decide⟩).lower ∧ (cell12493 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12493 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12493 ⟨24,by decide⟩).lower ∧ (cell12493 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12493 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12493 ⟨25,by decide⟩).lower ∧ (cell12493 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12493 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12493 ⟨26,by decide⟩).lower ∧ (cell12493 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12493 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12493 ⟨27,by decide⟩).lower ∧ (cell12493 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12493 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12493 ⟨28,by decide⟩).lower ∧ (cell12493 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12493 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12493 ⟨29,by decide⟩).lower ∧ (cell12493 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12493 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12493 ⟨30,by decide⟩).lower ∧ (cell12493 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12493 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12493 ⟨31,by decide⟩).lower ∧ (cell12493 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12493 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12493 ⟨32,by decide⟩).lower ∧ (cell12493 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12493 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12493 ⟨33,by decide⟩).lower ∧ (cell12493 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12493 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12493 ⟨34,by decide⟩).lower ∧ (cell12493 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12493 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12493 ⟨35,by decide⟩).lower ∧ (cell12493 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12493 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12493 ⟨36,by decide⟩).lower ∧ (cell12493 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12493 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12493 ⟨37,by decide⟩).lower ∧ (cell12493 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12493 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12493 ⟨38,by decide⟩).lower ∧ (cell12493 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12493 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12493 ⟨39,by decide⟩).lower ∧ (cell12493 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12493 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12493 ⟨40,by decide⟩).lower ∧ (cell12493 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12493 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12493 ⟨41,by decide⟩).lower ∧ (cell12493 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12493 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12493 ⟨42,by decide⟩).lower ∧ (cell12493 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12493 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12493 ⟨43,by decide⟩).lower ∧ (cell12493 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12493 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12493 ⟨44,by decide⟩).lower ∧ (cell12493 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12493 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12493 ⟨45,by decide⟩).lower ∧ (cell12493 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12493 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12493 ⟨46,by decide⟩).lower ∧ (cell12493 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12493 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12493 ⟨47,by decide⟩).lower ∧ (cell12493 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12493 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12493 ⟨48,by decide⟩).lower ∧ (cell12493 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12493 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12493 ⟨49,by decide⟩).lower ∧ (cell12493 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12493 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12493 ⟨50,by decide⟩).lower ∧ (cell12493 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12493 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12493 ⟨51,by decide⟩).lower ∧ (cell12493 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12493 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12493 ⟨52,by decide⟩).lower ∧ (cell12493 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12493 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12493 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12493 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12493,cell12493,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12493 i).lower ∧
    (cell12493 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12493 i).upper ≤ (0.532 : ℝ) ∧
    (cell12493 i).centre ≤ (0.1 : ℝ) ∧ (cell12493 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12493 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12493 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12493

/-! The local source numeric instances at 12493 have no network premises. -/
namespace BstLean.Part269.N12493
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12493)
open BstLean.Part268 (cell12493)

noncomputable def sourceNumerics12493 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12493 (cell12493 i)
      scalarRow12493.M scalarRow12493.H scalarRow12493.xi := by
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
    energy_allowance := scalarRow12493.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12493]
    centre_nonneg := (scalarRow12493.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12493])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12493
/-! Actual 12494 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12494 ≤ (1.036105830908 : ℝ) := by
  have hr : (111.776562838548 : ℝ) ≤ √(12494 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.776562838548 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12494 12494 (11 / 1000) ≤
    (0.008551766716 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12494) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.776562838548 : ℝ) ≤ √(12494 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12494)
  have hdiv : K / √(12494 : ℝ) ≤ K / 111.776562838548 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.776562838548 ≤ (0.008551766716 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12494.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12494 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12494 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12494 := gPlus_lower 12494
end BstLean.Part269.N12494

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12494
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036105830907 : ℝ) ≤ wn 12494 := by
  have hn : √(12494 : ℝ) ≤ 111.776562838549 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12494 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.776562838549 ≤ 2 / √(12494 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256107176 : ℝ) ≤ rhoBar 12494 BstLean.Part154.csC ∧
    rhoBar 12494 BstLean.Part154.csC ≤ 0.000256107572 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036105830907 : ℝ) / (1.295212 * 12494) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036105830908 : ℝ) / (1.29521 * 12494) := by gcongr
      _ ≤ (0.000256107572 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12494 BstLean.Part154.csC) ≤ 0.001024495880 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12494 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) ≤ 0.000195616844 ∧
    cc1 (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) ≤ 0.000124472265 ∧
    cc2 (rhoBar 12494 BstLean.Part154.csC) ≤ 0.000072257065 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12494 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12494 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12494 BstLean.Part154.csC * nuR (rhoBar 12494 BstLean.Part154.csC)) ≤ 0.000512231542 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256107572 : ℝ) * 0.001024495880 := by gcongr
      _ ≤ (0.000512231542 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12494 BstLean.Part154.csC) * nuR (rhoBar 12494 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024495880 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12494 BstLean.Part154.csC) * rhoBar 12494 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256107572 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256107572 / 2 + 0.399 * 0.001024495880 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195616844 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512231542 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124472265 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256107572 / 1.414213562 := by gcongr
      _ ≤ (0.000072257065 : ℝ) := by norm_num

end BstLean.Part269.N12494

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12494
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) ≤ 1.65252E-7 := by
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12494 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12494 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12494 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195616844 : ℝ) ^ 2 + 0.000124472265 ^ 2 + 3 * 0.000072257065 ^ 2 +
        2 * 0.797885 * 0.000195616844 * 0.000124472265 + 2 * 0.000195616844 * 0.000072257065 +
        4 * 0.797885 * 0.000124472265 * 0.000072257065 := by gcongr
    _ ≤ (1.65252E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12494 BstLean.Part154.csC Θ ≤ 0.002674170454 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12494 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12494 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12494 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036105830908 * 1.65252E-7 / (0.000256107176 : ℝ) := by gcongr
    _ ≤ 0.002674170454 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12494 BstLean.Part154.csC Θ ≤ 0.002967990199 + 0.000675719951 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12494 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12494 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036105830908 : ℝ) * ((2 * Θ * 0.000256107572 +
        (6863 / 10000) * 0.000256107572 * 12494 * 0.001024495880) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002967990199 + 0.000675719951 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12494 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12494 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12494 0.011 Θ ∧ gammaRatio 12494 0.011 Θ ≤ 0.000088043161 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12494 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036105830908 : ℝ) * 0.525 / ((1 - 0.011) * 12494) := by gcongr
      _ ≤ (0.000088043161 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12494 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12494 0.011 Θ) :=
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
    badAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12494 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12494 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12494 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12494 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12494 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12494 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12494 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12494 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12494 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12494 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036105830908 : ℝ) * 12494 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003785329361 + 0.003349890405 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12494

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12494
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12494 BstLean.Part154.csC) (piBar (rhoBar 12494 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12494 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12494 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12494 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12494 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12494 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12494 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12494 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12494 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12494 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12494 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052919933195 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12494) ≤ 0.010684150154 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12494 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036105830908)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010684150154 + 2 * 0.737676 / 12494) := by gcongr
    _ ≤ (0.052919933195 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12494 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12494

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12494
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494098759 : ℝ) ≤ plow 12494 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12494) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050621824)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403939489) : eMP 12494 0.011 xi bn ≤ 0.001208384253 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12494 : ℝ) * (1 - 0.011))) ≤ 0.000597448203 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403939489 / (12494 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597448203 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597448203 : ℝ) + 3.141593 * 0.053050621824 / (12494 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208384253 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050621824)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403939489) : PiBarMP 12494 12 0.011 xi bn ≤ 0.162588811121 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12494 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037469180523 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.160091759587 : ℝ) ≤ √((12494 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.776562838548 : ℝ) ≤ √(12494 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12494) ≤ 0.124645166294 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037469180523 + 0.053050621824 * 1.772454 / (2 * (111.160091759587 : ℝ))) * (1 + 0.001208384253) +
        8 / (12494 * 111.776562838548) + 0.124645166294 := by gcongr
    _ ≤ (0.162588811121 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050621824)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403939489) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283247139196) :
    parallelOracle 12494 0.011 xi bn cd ≤ 0.163596644706 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12494 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12494 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494098759 : ℝ) ≤ plow 12494 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.776562838548 : ℝ) ≤ √(12494 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283247139196 : ℝ) / (2 * 0.560494098759 * 111.776562838548)) * 0.162588811121 +
        0.283247139196 ^ 2 / (2 * 0.560494098759 * 111.776562838548) := by gcongr
    _ ≤ (0.163596644706 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050621824) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403939489)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283247139196) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12494 12494 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494098759 : ℝ) ≤ plow 12494 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.776562838548 : ℝ) ≤ √(12494 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12494 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12494 Θ 1.22 ≤ 0.011863851119 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.776562838548 := by gcongr <;> linarith
      _ ≤ (0.011863851119 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12494 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12494 12494 0.011 ≤ 0.008551766716 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12494 12494 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12494 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12494 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12494 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12494 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163596644706 + 0.011863851119 + (0.008551766716 : ℝ) *
        (1 + 2 * (0.283247139196 + 0.011863851119) / (0.560494098759 * 111.776562838548))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12494]

end BstLean.Part269.N12494

/-! The original eight local profiles supply actual 12494 moment certificates. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12494 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053050621824 ∧
    0 ≤ bN 12494 BstLean.Part154.csC (groupTheta g) ∧ bN 12494 BstLean.Part154.csC (groupTheta g) ≤ 0.001403939489 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12494 12494 0.011
      (momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12494 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12494 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12494 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230327206001 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12494 0.011
      (momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12494 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12494
/-! The actual computed-centre upper energy formula at 12494. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12494

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12494)
open BstLean.Part268 (cell12494)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086115724061
  | 2 => 0.087070544800
  | 3 => 0.088025358016
  | 4 => 0.088982001567
  | 5 => 0.089942683354
  | 6 => 0.090910034289
  | 7 => 0.091887165877
  | 8 => 0.092877732404
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12494 12494 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12494 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12494

/-! Actual upper energy certificates on all 43 source endpoints at 12494. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12494)
open BstLean.Part268 (cell12494)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12494 (gMinus 12494) (1 - (cell12494 i).lower) ≤ 1 ∧
    energyUpper 12494 (gMinus 12494) (BstLean.Part211.gPlus 12494)
      (finiteEnergy 12494 12494 0.011) (1 - (cell12494 i).lower) ≤
      (cell12494 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨10,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨11,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨12,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨13,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨14,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨15,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨16,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨17,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨18,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨19,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨20,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨21,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨22,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨23,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨24,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨25,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨26,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨27,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨28,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨29,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨30,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨31,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨32,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨33,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨34,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨35,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨36,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨37,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨38,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨39,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨40,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨41,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨42,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨43,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨44,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨45,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨46,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨47,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨48,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨49,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨50,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨51,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12494) (by norm_num)
        (q := 1 - (cell12494 ⟨52,by decide⟩).lower)
        (by norm_num [cell12494]) (by norm_num [cell12494])
      exact ⟨E.1,E.2.trans (by norm_num [cell12494])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12494

/-! Source-cell containment and simple scalar guards at 12494. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12494)
open BstLean.Part268 (cell12494)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12494 ⟨10,by decide⟩).lower ∧ (cell12494 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12494 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12494 ⟨11,by decide⟩).lower ∧ (cell12494 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12494 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12494 ⟨12,by decide⟩).lower ∧ (cell12494 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12494 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12494 ⟨13,by decide⟩).lower ∧ (cell12494 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12494 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12494 ⟨14,by decide⟩).lower ∧ (cell12494 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12494 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12494 ⟨15,by decide⟩).lower ∧ (cell12494 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12494 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12494 ⟨16,by decide⟩).lower ∧ (cell12494 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12494 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12494 ⟨17,by decide⟩).lower ∧ (cell12494 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12494 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12494 ⟨18,by decide⟩).lower ∧ (cell12494 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12494 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12494 ⟨19,by decide⟩).lower ∧ (cell12494 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12494 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12494 ⟨20,by decide⟩).lower ∧ (cell12494 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12494 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12494 ⟨21,by decide⟩).lower ∧ (cell12494 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12494 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12494 ⟨22,by decide⟩).lower ∧ (cell12494 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12494 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12494 ⟨23,by decide⟩).lower ∧ (cell12494 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12494 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12494 ⟨24,by decide⟩).lower ∧ (cell12494 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12494 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12494 ⟨25,by decide⟩).lower ∧ (cell12494 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12494 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12494 ⟨26,by decide⟩).lower ∧ (cell12494 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12494 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12494 ⟨27,by decide⟩).lower ∧ (cell12494 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12494 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12494 ⟨28,by decide⟩).lower ∧ (cell12494 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12494 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12494 ⟨29,by decide⟩).lower ∧ (cell12494 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12494 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12494 ⟨30,by decide⟩).lower ∧ (cell12494 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12494 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12494 ⟨31,by decide⟩).lower ∧ (cell12494 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12494 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12494 ⟨32,by decide⟩).lower ∧ (cell12494 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12494 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12494 ⟨33,by decide⟩).lower ∧ (cell12494 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12494 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12494 ⟨34,by decide⟩).lower ∧ (cell12494 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12494 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12494 ⟨35,by decide⟩).lower ∧ (cell12494 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12494 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12494 ⟨36,by decide⟩).lower ∧ (cell12494 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12494 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12494 ⟨37,by decide⟩).lower ∧ (cell12494 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12494 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12494 ⟨38,by decide⟩).lower ∧ (cell12494 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12494 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12494 ⟨39,by decide⟩).lower ∧ (cell12494 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12494 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12494 ⟨40,by decide⟩).lower ∧ (cell12494 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12494 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12494 ⟨41,by decide⟩).lower ∧ (cell12494 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12494 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12494 ⟨42,by decide⟩).lower ∧ (cell12494 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12494 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12494 ⟨43,by decide⟩).lower ∧ (cell12494 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12494 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12494 ⟨44,by decide⟩).lower ∧ (cell12494 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12494 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12494 ⟨45,by decide⟩).lower ∧ (cell12494 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12494 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12494 ⟨46,by decide⟩).lower ∧ (cell12494 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12494 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12494 ⟨47,by decide⟩).lower ∧ (cell12494 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12494 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12494 ⟨48,by decide⟩).lower ∧ (cell12494 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12494 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12494 ⟨49,by decide⟩).lower ∧ (cell12494 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12494 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12494 ⟨50,by decide⟩).lower ∧ (cell12494 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12494 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12494 ⟨51,by decide⟩).lower ∧ (cell12494 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12494 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12494 ⟨52,by decide⟩).lower ∧ (cell12494 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12494 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12494 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12494 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12494,cell12494,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12494 i).lower ∧
    (cell12494 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12494 i).upper ≤ (0.532 : ℝ) ∧
    (cell12494 i).centre ≤ (0.1 : ℝ) ∧ (cell12494 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12494 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12494 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12494

/-! The local source numeric instances at 12494 have no network premises. -/
namespace BstLean.Part269.N12494
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12494)
open BstLean.Part268 (cell12494)

noncomputable def sourceNumerics12494 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12494 (cell12494 i)
      scalarRow12494.M scalarRow12494.H scalarRow12494.xi := by
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
    energy_allowance := scalarRow12494.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12494]
    centre_nonneg := (scalarRow12494.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12494])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12494
/-! Actual 12495 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12495 ≤ (1.036104373257 : ℝ) := by
  have hr : (111.781035958699 : ℝ) ≤ √(12495 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.781035958699 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12495 12495 (11 / 1000) ≤
    (0.008551424499 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12495) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.781035958699 : ℝ) ≤ √(12495 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12495)
  have hdiv : K / √(12495 : ℝ) ≤ K / 111.781035958699 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.781035958699 ≤ (0.008551424499 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12495.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12495 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12495 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12495 := gPlus_lower 12495
end BstLean.Part269.N12495

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12495
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036104373256 : ℝ) ≤ wn 12495 := by
  have hn : √(12495 : ℝ) ≤ 111.781035958700 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12495 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.781035958700 ≤ 2 / √(12495 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256086319 : ℝ) ≤ rhoBar 12495 BstLean.Part154.csC ∧
    rhoBar 12495 BstLean.Part154.csC ≤ 0.000256086715 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036104373256 : ℝ) / (1.295212 * 12495) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036104373257 : ℝ) / (1.29521 * 12495) := by gcongr
      _ ≤ (0.000256086715 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12495 BstLean.Part154.csC) ≤ 0.001024412441 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12495 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) ≤ 0.000195600912 ∧
    cc1 (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) ≤ 0.000124462128 ∧
    cc2 (rhoBar 12495 BstLean.Part154.csC) ≤ 0.000072251181 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12495 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12495 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12495 BstLean.Part154.csC * nuR (rhoBar 12495 BstLean.Part154.csC)) ≤ 0.000512189825 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256086715 : ℝ) * 0.001024412441 := by gcongr
      _ ≤ (0.000512189825 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12495 BstLean.Part154.csC) * nuR (rhoBar 12495 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024412441 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12495 BstLean.Part154.csC) * rhoBar 12495 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256086715 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256086715 / 2 + 0.399 * 0.001024412441 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195600912 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512189825 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124462128 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256086715 / 1.414213562 := by gcongr
      _ ≤ (0.000072251181 : ℝ) := by norm_num

end BstLean.Part269.N12495

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12495
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) ≤ 1.65225E-7 := by
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12495 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12495 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12495 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195600912 : ℝ) ^ 2 + 0.000124462128 ^ 2 + 3 * 0.000072251181 ^ 2 +
        2 * 0.797885 * 0.000195600912 * 0.000124462128 + 2 * 0.000195600912 * 0.000072251181 +
        4 * 0.797885 * 0.000124462128 * 0.000072251181 := by gcongr
    _ ≤ (1.65225E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12495 BstLean.Part154.csC Θ ≤ 0.002673947531 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12495 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12495 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12495 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036104373257 * 1.65225E-7 / (0.000256086319 : ℝ) := by gcongr
    _ ≤ 0.002673947531 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12495 BstLean.Part154.csC Θ ≤ 0.002967740125 + 0.000675663970 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12495 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12495 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036104373257 : ℝ) * ((2 * Θ * 0.000256086715 +
        (6863 / 10000) * 0.000256086715 * 12495 * 0.001024412441) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002967740125 + 0.000675663970 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12495 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12495 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12495 0.011 Θ ∧ gammaRatio 12495 0.011 Θ ≤ 0.000088035991 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12495 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036104373257 : ℝ) * 0.525 / ((1 - 0.011) * 12495) := by gcongr
      _ ≤ (0.000088035991 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12495 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12495 0.011 Θ) :=
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
    badAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12495 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12495 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12495 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12495 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12495 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12495 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12495 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12495 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12495 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12495 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036104373257 : ℝ) * 12495 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003785079287 + 0.003349611501 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12495

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12495
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12495 BstLean.Part154.csC) (piBar (rhoBar 12495 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12495 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12495 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12495 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12495 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12495 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12495 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12495 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12495 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12495 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12495 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052917792362 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12495) ≤ 0.010683722609 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12495 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036104373257)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010683722609 + 2 * 0.737676 / 12495) := by gcongr
    _ ≤ (0.052917792362 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12495 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12495

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12495
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494145482 : ℝ) ≤ plow 12495 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12495) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050225326)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403822454) : eMP 12495 0.011 xi bn ≤ 0.001208285452 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12495 : ℝ) * (1 - 0.011))) ≤ 0.000597399393 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403822454 / (12495 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597399393 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597399393 : ℝ) + 3.141593 * 0.053050225326 / (12495 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208285452 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050225326)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403822454) : PiBarMP 12495 12 0.011 xi bn ≤ 0.162582235008 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12495 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037467618740 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.164540209547 : ℝ) ≤ √((12495 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.781035958699 : ℝ) ≤ √(12495 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12495) ≤ 0.124640178393 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037467618740 + 0.053050225326 * 1.772454 / (2 * (111.164540209547 : ℝ))) * (1 + 0.001208285452) +
        8 / (12495 * 111.781035958699) + 0.124640178393 := by gcongr
    _ ≤ (0.162582235008 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050225326)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403822454) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283244137634) :
    parallelOracle 12495 0.011 xi bn cd ≤ 0.163589995850 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12495 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12495 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494145482 : ℝ) ≤ plow 12495 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.781035958699 : ℝ) ≤ √(12495 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283244137634 : ℝ) / (2 * 0.560494145482 * 111.781035958699)) * 0.162582235008 +
        0.283244137634 ^ 2 / (2 * 0.560494145482 * 111.781035958699) := by gcongr
    _ ≤ (0.163589995850 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053050225326) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403822454)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283244137634) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12495 12495 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494145482 : ℝ) ≤ plow 12495 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.781035958699 : ℝ) ≤ √(12495 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12495 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12495 Θ 1.22 ≤ 0.011863376365 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.781035958699 := by gcongr <;> linarith
      _ ≤ (0.011863376365 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12495 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12495 12495 0.011 ≤ 0.008551424499 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12495 12495 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12495 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12495 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12495 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12495 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163589995850 + 0.011863376365 + (0.008551424499 : ℝ) *
        (1 + 2 * (0.283244137634 + 0.011863376365) / (0.560494145482 * 111.781035958699))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12495]

end BstLean.Part269.N12495

/-! The original eight local profiles supply actual 12495 moment certificates. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12495 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053050225326 ∧
    0 ≤ bN 12495 BstLean.Part154.csC (groupTheta g) ∧ bN 12495 BstLean.Part154.csC (groupTheta g) ≤ 0.001403822454 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12495 12495 0.011
      (momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12495 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12495 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12495 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230326345272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12495 0.011
      (momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12495 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12495
/-! The actual computed-centre upper energy formula at 12495. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12495

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12495)
open BstLean.Part268 (cell12495)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086112559636
  | 2 => 0.087067316313
  | 3 => 0.088022055194
  | 4 => 0.088978611843
  | 5 => 0.089939191476
  | 6 => 0.090906421881
  | 7 => 0.091883410955
  | 8 => 0.092873808835
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12495 12495 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12495 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12495

/-! Actual upper energy certificates on all 43 source endpoints at 12495. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12495)
open BstLean.Part268 (cell12495)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12495 (gMinus 12495) (1 - (cell12495 i).lower) ≤ 1 ∧
    energyUpper 12495 (gMinus 12495) (BstLean.Part211.gPlus 12495)
      (finiteEnergy 12495 12495 0.011) (1 - (cell12495 i).lower) ≤
      (cell12495 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨10,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨11,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨12,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨13,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨14,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨15,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨16,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨17,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨18,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨19,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨20,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨21,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨22,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨23,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨24,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨25,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨26,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨27,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨28,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨29,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨30,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨31,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨32,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨33,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨34,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨35,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨36,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨37,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨38,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨39,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨40,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨41,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨42,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨43,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨44,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨45,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨46,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨47,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨48,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨49,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨50,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨51,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12495) (by norm_num)
        (q := 1 - (cell12495 ⟨52,by decide⟩).lower)
        (by norm_num [cell12495]) (by norm_num [cell12495])
      exact ⟨E.1,E.2.trans (by norm_num [cell12495])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12495

/-! Source-cell containment and simple scalar guards at 12495. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12495)
open BstLean.Part268 (cell12495)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12495 ⟨10,by decide⟩).lower ∧ (cell12495 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12495 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12495 ⟨11,by decide⟩).lower ∧ (cell12495 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12495 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12495 ⟨12,by decide⟩).lower ∧ (cell12495 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12495 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12495 ⟨13,by decide⟩).lower ∧ (cell12495 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12495 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12495 ⟨14,by decide⟩).lower ∧ (cell12495 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12495 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12495 ⟨15,by decide⟩).lower ∧ (cell12495 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12495 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12495 ⟨16,by decide⟩).lower ∧ (cell12495 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12495 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12495 ⟨17,by decide⟩).lower ∧ (cell12495 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12495 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12495 ⟨18,by decide⟩).lower ∧ (cell12495 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12495 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12495 ⟨19,by decide⟩).lower ∧ (cell12495 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12495 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12495 ⟨20,by decide⟩).lower ∧ (cell12495 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12495 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12495 ⟨21,by decide⟩).lower ∧ (cell12495 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12495 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12495 ⟨22,by decide⟩).lower ∧ (cell12495 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12495 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12495 ⟨23,by decide⟩).lower ∧ (cell12495 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12495 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12495 ⟨24,by decide⟩).lower ∧ (cell12495 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12495 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12495 ⟨25,by decide⟩).lower ∧ (cell12495 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12495 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12495 ⟨26,by decide⟩).lower ∧ (cell12495 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12495 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12495 ⟨27,by decide⟩).lower ∧ (cell12495 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12495 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12495 ⟨28,by decide⟩).lower ∧ (cell12495 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12495 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12495 ⟨29,by decide⟩).lower ∧ (cell12495 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12495 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12495 ⟨30,by decide⟩).lower ∧ (cell12495 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12495 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12495 ⟨31,by decide⟩).lower ∧ (cell12495 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12495 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12495 ⟨32,by decide⟩).lower ∧ (cell12495 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12495 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12495 ⟨33,by decide⟩).lower ∧ (cell12495 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12495 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12495 ⟨34,by decide⟩).lower ∧ (cell12495 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12495 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12495 ⟨35,by decide⟩).lower ∧ (cell12495 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12495 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12495 ⟨36,by decide⟩).lower ∧ (cell12495 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12495 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12495 ⟨37,by decide⟩).lower ∧ (cell12495 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12495 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12495 ⟨38,by decide⟩).lower ∧ (cell12495 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12495 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12495 ⟨39,by decide⟩).lower ∧ (cell12495 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12495 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12495 ⟨40,by decide⟩).lower ∧ (cell12495 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12495 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12495 ⟨41,by decide⟩).lower ∧ (cell12495 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12495 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12495 ⟨42,by decide⟩).lower ∧ (cell12495 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12495 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12495 ⟨43,by decide⟩).lower ∧ (cell12495 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12495 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12495 ⟨44,by decide⟩).lower ∧ (cell12495 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12495 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12495 ⟨45,by decide⟩).lower ∧ (cell12495 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12495 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12495 ⟨46,by decide⟩).lower ∧ (cell12495 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12495 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12495 ⟨47,by decide⟩).lower ∧ (cell12495 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12495 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12495 ⟨48,by decide⟩).lower ∧ (cell12495 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12495 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12495 ⟨49,by decide⟩).lower ∧ (cell12495 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12495 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12495 ⟨50,by decide⟩).lower ∧ (cell12495 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12495 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12495 ⟨51,by decide⟩).lower ∧ (cell12495 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12495 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12495 ⟨52,by decide⟩).lower ∧ (cell12495 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12495 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12495 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12495 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12495,cell12495,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12495 i).lower ∧
    (cell12495 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12495 i).upper ≤ (0.532 : ℝ) ∧
    (cell12495 i).centre ≤ (0.1 : ℝ) ∧ (cell12495 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12495 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12495 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12495

/-! The local source numeric instances at 12495 have no network premises. -/
namespace BstLean.Part269.N12495
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12495)
open BstLean.Part268 (cell12495)

noncomputable def sourceNumerics12495 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12495 (cell12495 i)
      scalarRow12495.M scalarRow12495.H scalarRow12495.xi := by
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
    energy_allowance := scalarRow12495.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12495]
    centre_nonneg := (scalarRow12495.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12495])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12495
/-! Actual 12496 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12496 ≤ (1.036102915782 : ℝ) := by
  have hr : (111.785508899856 : ℝ) ≤ √(12496 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.785508899856 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12496 12496 (11 / 1000) ≤
    (0.008551082323 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12496) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.785508899856 : ℝ) ≤ √(12496 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12496)
  have hdiv : K / √(12496 : ℝ) ≤ K / 111.785508899856 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.785508899856 ≤ (0.008551082323 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12496.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12496 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12496 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12496 := gPlus_lower 12496
end BstLean.Part269.N12496

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12496
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036102915781 : ℝ) ≤ wn 12496 := by
  have hn : √(12496 : ℝ) ≤ 111.785508899857 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12496 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.785508899857 ≤ 2 / √(12496 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256065465 : ℝ) ≤ rhoBar 12496 BstLean.Part154.csC ∧
    rhoBar 12496 BstLean.Part154.csC ≤ 0.000256065862 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036102915781 : ℝ) / (1.295212 * 12496) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036102915782 : ℝ) / (1.29521 * 12496) := by gcongr
      _ ≤ (0.000256065862 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12496 BstLean.Part154.csC) ≤ 0.001024329018 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12496 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) ≤ 0.000195584984 ∧
    cc1 (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) ≤ 0.000124451993 ∧
    cc2 (rhoBar 12496 BstLean.Part154.csC) ≤ 0.000072245298 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12496 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12496 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12496 BstLean.Part154.csC * nuR (rhoBar 12496 BstLean.Part154.csC)) ≤ 0.000512148117 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256065862 : ℝ) * 0.001024329018 := by gcongr
      _ ≤ (0.000512148117 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12496 BstLean.Part154.csC) * nuR (rhoBar 12496 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024329018 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12496 BstLean.Part154.csC) * rhoBar 12496 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256065862 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256065862 / 2 + 0.399 * 0.001024329018 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195584984 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512148117 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124451993 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256065862 / 1.414213562 := by gcongr
      _ ≤ (0.000072245298 : ℝ) := by norm_num

end BstLean.Part269.N12496

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12496
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) ≤ 1.65199E-7 := by
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12496 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12496 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12496 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195584984 : ℝ) ^ 2 + 0.000124451993 ^ 2 + 3 * 0.000072245298 ^ 2 +
        2 * 0.797885 * 0.000195584984 * 0.000124451993 + 2 * 0.000195584984 * 0.000072245298 +
        4 * 0.797885 * 0.000124451993 * 0.000072245298 := by gcongr
    _ ≤ (1.65199E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12496 BstLean.Part154.csC Θ ≤ 0.002673740727 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12496 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12496 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12496 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036102915782 * 1.65199E-7 / (0.000256065465 : ℝ) := by gcongr
    _ ≤ 0.002673740727 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12496 BstLean.Part154.csC Θ ≤ 0.002967490106 + 0.000675608001 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12496 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12496 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036102915782 : ℝ) * ((2 * Θ * 0.000256065862 +
        (6863 / 10000) * 0.000256065862 * 12496 * 0.001024329018) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002967490106 + 0.000675608001 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12496 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12496 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12496 0.011 Θ ∧ gammaRatio 12496 0.011 Θ ≤ 0.000088028822 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12496 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036102915782 : ℝ) * 0.525 / ((1 - 0.011) * 12496) := by gcongr
      _ ≤ (0.000088028822 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12496 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12496 0.011 Θ) :=
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
    badAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12496 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12496 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12496 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12496 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12496 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12496 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12496 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12496 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12496 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12496 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036102915782 : ℝ) * 12496 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003784829268 + 0.003349348728 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12496

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12496
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12496 BstLean.Part154.csC) (piBar (rhoBar 12496 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12496 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12496 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12496 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12496 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12496 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12496 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12496 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12496 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12496 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12496 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052915651787 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12496) ≤ 0.010683295115 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12496 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036102915782)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010683295115 + 2 * 0.737676 / 12496) := by gcongr
    _ ≤ (0.052915651787 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12496 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12496

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12496
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494192197 : ℝ) ≤ plow 12496 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12496) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049837351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403713882) : eMP 12496 0.011 xi bn ≤ 0.001208190265 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12496 : ℝ) * (1 - 0.011))) ≤ 0.000597352388 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403713882 / (12496 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597352388 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597352388 : ℝ) + 3.141593 * 0.053049837351 / (12496 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208190265 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049837351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403713882) : PiBarMP 12496 12 0.011 xi bn ≤ 0.162575772715 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12496 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037466169834 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.168988481500 : ℝ) ≤ √((12496 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.785508899856 : ℝ) ≤ √(12496 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12496) ≤ 0.124635191090 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037466169834 + 0.053049837351 * 1.772454 / (2 * (111.168988481500 : ℝ))) * (1 + 0.001208190265) +
        8 / (12496 * 111.785508899856) + 0.124635191090 := by gcongr
    _ ≤ (0.162575772715 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049837351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403713882) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283241154828) :
    parallelOracle 12496 0.011 xi bn cd ≤ 0.163583461187 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12496 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12496 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494192197 : ℝ) ≤ plow 12496 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.785508899856 : ℝ) ≤ √(12496 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283241154828 : ℝ) / (2 * 0.560494192197 * 111.785508899856)) * 0.162575772715 +
        0.283241154828 ^ 2 / (2 * 0.560494192197 * 111.785508899856) := by gcongr
    _ ≤ (0.163583461187 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049837351) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403713882)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283241154828) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12496 12496 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494192197 : ℝ) ≤ plow 12496 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.785508899856 : ℝ) ≤ √(12496 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12496 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12496 Θ 1.22 ≤ 0.011862901669 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.785508899856 := by gcongr <;> linarith
      _ ≤ (0.011862901669 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12496 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12496 12496 0.011 ≤ 0.008551082323 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12496 12496 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12496 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12496 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12496 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12496 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163583461187 + 0.011862901669 + (0.008551082323 : ℝ) *
        (1 + 2 * (0.283241154828 + 0.011862901669) / (0.560494192197 * 111.785508899856))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12496]

end BstLean.Part269.N12496

/-! The original eight local profiles supply actual 12496 moment certificates. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12496 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053049837351 ∧
    0 ≤ bN 12496 BstLean.Part154.csC (groupTheta g) ∧ bN 12496 BstLean.Part154.csC (groupTheta g) ≤ 0.001403713882 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12496 12496 0.011
      (momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12496 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12496 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12496 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230325503041 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12496 0.011
      (momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12496 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12496
/-! The actual computed-centre upper energy formula at 12496. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12496

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12496)
open BstLean.Part268 (cell12496)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086109396552
  | 2 => 0.087064089226
  | 3 => 0.088018753843
  | 4 => 0.088975223678
  | 5 => 0.089935701264
  | 6 => 0.090902811271
  | 7 => 0.091879657987
  | 8 => 0.092869887409
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12496 12496 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12496 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12496

/-! Actual upper energy certificates on all 43 source endpoints at 12496. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12496)
open BstLean.Part268 (cell12496)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12496 (gMinus 12496) (1 - (cell12496 i).lower) ≤ 1 ∧
    energyUpper 12496 (gMinus 12496) (BstLean.Part211.gPlus 12496)
      (finiteEnergy 12496 12496 0.011) (1 - (cell12496 i).lower) ≤
      (cell12496 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨10,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨11,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨12,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨13,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨14,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨15,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨16,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨17,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨18,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨19,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨20,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨21,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨22,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨23,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨24,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨25,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨26,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨27,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨28,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨29,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨30,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨31,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨32,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨33,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨34,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨35,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨36,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨37,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨38,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨39,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨40,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨41,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨42,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨43,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨44,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨45,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨46,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨47,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨48,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨49,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨50,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨51,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12496) (by norm_num)
        (q := 1 - (cell12496 ⟨52,by decide⟩).lower)
        (by norm_num [cell12496]) (by norm_num [cell12496])
      exact ⟨E.1,E.2.trans (by norm_num [cell12496])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12496

/-! Source-cell containment and simple scalar guards at 12496. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12496)
open BstLean.Part268 (cell12496)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12496 ⟨10,by decide⟩).lower ∧ (cell12496 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12496 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12496 ⟨11,by decide⟩).lower ∧ (cell12496 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12496 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12496 ⟨12,by decide⟩).lower ∧ (cell12496 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12496 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12496 ⟨13,by decide⟩).lower ∧ (cell12496 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12496 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12496 ⟨14,by decide⟩).lower ∧ (cell12496 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12496 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12496 ⟨15,by decide⟩).lower ∧ (cell12496 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12496 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12496 ⟨16,by decide⟩).lower ∧ (cell12496 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12496 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12496 ⟨17,by decide⟩).lower ∧ (cell12496 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12496 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12496 ⟨18,by decide⟩).lower ∧ (cell12496 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12496 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12496 ⟨19,by decide⟩).lower ∧ (cell12496 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12496 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12496 ⟨20,by decide⟩).lower ∧ (cell12496 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12496 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12496 ⟨21,by decide⟩).lower ∧ (cell12496 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12496 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12496 ⟨22,by decide⟩).lower ∧ (cell12496 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12496 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12496 ⟨23,by decide⟩).lower ∧ (cell12496 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12496 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12496 ⟨24,by decide⟩).lower ∧ (cell12496 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12496 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12496 ⟨25,by decide⟩).lower ∧ (cell12496 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12496 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12496 ⟨26,by decide⟩).lower ∧ (cell12496 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12496 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12496 ⟨27,by decide⟩).lower ∧ (cell12496 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12496 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12496 ⟨28,by decide⟩).lower ∧ (cell12496 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12496 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12496 ⟨29,by decide⟩).lower ∧ (cell12496 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12496 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12496 ⟨30,by decide⟩).lower ∧ (cell12496 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12496 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12496 ⟨31,by decide⟩).lower ∧ (cell12496 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12496 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12496 ⟨32,by decide⟩).lower ∧ (cell12496 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12496 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12496 ⟨33,by decide⟩).lower ∧ (cell12496 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12496 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12496 ⟨34,by decide⟩).lower ∧ (cell12496 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12496 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12496 ⟨35,by decide⟩).lower ∧ (cell12496 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12496 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12496 ⟨36,by decide⟩).lower ∧ (cell12496 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12496 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12496 ⟨37,by decide⟩).lower ∧ (cell12496 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12496 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12496 ⟨38,by decide⟩).lower ∧ (cell12496 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12496 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12496 ⟨39,by decide⟩).lower ∧ (cell12496 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12496 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12496 ⟨40,by decide⟩).lower ∧ (cell12496 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12496 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12496 ⟨41,by decide⟩).lower ∧ (cell12496 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12496 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12496 ⟨42,by decide⟩).lower ∧ (cell12496 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12496 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12496 ⟨43,by decide⟩).lower ∧ (cell12496 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12496 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12496 ⟨44,by decide⟩).lower ∧ (cell12496 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12496 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12496 ⟨45,by decide⟩).lower ∧ (cell12496 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12496 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12496 ⟨46,by decide⟩).lower ∧ (cell12496 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12496 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12496 ⟨47,by decide⟩).lower ∧ (cell12496 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12496 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12496 ⟨48,by decide⟩).lower ∧ (cell12496 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12496 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12496 ⟨49,by decide⟩).lower ∧ (cell12496 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12496 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12496 ⟨50,by decide⟩).lower ∧ (cell12496 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12496 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12496 ⟨51,by decide⟩).lower ∧ (cell12496 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12496 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12496 ⟨52,by decide⟩).lower ∧ (cell12496 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12496 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12496 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12496 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12496,cell12496,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12496 i).lower ∧
    (cell12496 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12496 i).upper ≤ (0.532 : ℝ) ∧
    (cell12496 i).centre ≤ (0.1 : ℝ) ∧ (cell12496 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12496 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12496 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12496

/-! The local source numeric instances at 12496 have no network premises. -/
namespace BstLean.Part269.N12496
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12496)
open BstLean.Part268 (cell12496)

noncomputable def sourceNumerics12496 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12496 (cell12496 i)
      scalarRow12496.M scalarRow12496.H scalarRow12496.xi := by
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
    energy_allowance := scalarRow12496.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12496]
    centre_nonneg := (scalarRow12496.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12496])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12496
/-! Actual 12497 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12497 ≤ (1.036101458482 : ℝ) := by
  have hr : (111.789981662043 : ℝ) ≤ √(12497 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.789981662043 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12497 12497 (11 / 1000) ≤
    (0.008550740188 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12497) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.789981662043 : ℝ) ≤ √(12497 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12497)
  have hdiv : K / √(12497 : ℝ) ≤ K / 111.789981662043 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.789981662043 ≤ (0.008550740188 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12497.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12497 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12497 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12497 := gPlus_lower 12497
end BstLean.Part269.N12497

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12497
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036101458481 : ℝ) ≤ wn 12497 := by
  have hn : √(12497 : ℝ) ≤ 111.789981662044 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12497 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.789981662044 ≤ 2 / √(12497 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256044615 : ℝ) ≤ rhoBar 12497 BstLean.Part154.csC ∧
    rhoBar 12497 BstLean.Part154.csC ≤ 0.000256045011 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036101458481 : ℝ) / (1.295212 * 12497) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036101458482 : ℝ) / (1.29521 * 12497) := by gcongr
      _ ≤ (0.000256045011 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12497 BstLean.Part154.csC) ≤ 0.001024245604 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12497 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) ≤ 0.000195569057 ∧
    cc1 (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) ≤ 0.000124441859 ∧
    cc2 (rhoBar 12497 BstLean.Part154.csC) ≤ 0.000072239415 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12497 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12497 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12497 BstLean.Part154.csC * nuR (rhoBar 12497 BstLean.Part154.csC)) ≤ 0.000512106412 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256045011 : ℝ) * 0.001024245604 := by gcongr
      _ ≤ (0.000512106412 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12497 BstLean.Part154.csC) * nuR (rhoBar 12497 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024245604 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12497 BstLean.Part154.csC) * rhoBar 12497 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256045011 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256045011 / 2 + 0.399 * 0.001024245604 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195569057 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512106412 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124441859 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256045011 / 1.414213562 := by gcongr
      _ ≤ (0.000072239415 : ℝ) := by norm_num

end BstLean.Part269.N12497

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12497
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) ≤ 1.65172E-7 := by
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12497 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12497 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12497 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195569057 : ℝ) ^ 2 + 0.000124441859 ^ 2 + 3 * 0.000072239415 ^ 2 +
        2 * 0.797885 * 0.000195569057 * 0.000124441859 + 2 * 0.000195569057 * 0.000072239415 +
        4 * 0.797885 * 0.000124441859 * 0.000072239415 := by gcongr
    _ ≤ (1.65172E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12497 BstLean.Part154.csC Θ ≤ 0.002673517662 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12497 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12497 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12497 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036101458482 * 1.65172E-7 / (0.000256044615 : ℝ) := by gcongr
    _ ≤ 0.002673517662 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12497 BstLean.Part154.csC Θ ≤ 0.002967240100 + 0.000675552037 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12497 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12497 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036101458482 : ℝ) * ((2 * Θ * 0.000256045011 +
        (6863 / 10000) * 0.000256045011 * 12497 * 0.001024245604) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002967240100 + 0.000675552037 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12497 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12497 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12497 0.011 Θ ∧ gammaRatio 12497 0.011 Θ ≤ 0.000088021654 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12497 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036101458482 : ℝ) * 0.525 / ((1 - 0.011) * 12497) := by gcongr
      _ ≤ (0.000088021654 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12497 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12497 0.011 Θ) :=
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
    badAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12497 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12497 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12497 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12497 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12497 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12497 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12497 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12497 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12497 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12497 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036101458482 : ℝ) * 12497 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003784579262 + 0.003349069699 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12497

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12497
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12497 BstLean.Part154.csC) (piBar (rhoBar 12497 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12497 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12497 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12497 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12497 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12497 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12497 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12497 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12497 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12497 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12497 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052913511469 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12497) ≤ 0.010682867672 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12497 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036101458482)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010682867672 + 2 * 0.737676 / 12497) := by gcongr
    _ ≤ (0.052913511469 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12497 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12497

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12497
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494238905 : ℝ) ≤ plow 12497 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12497) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049440854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403596773) : eMP 12497 0.011 xi bn ≤ 0.001208091449 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12497 : ℝ) * (1 - 0.011))) ≤ 0.000597303570 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403596773 / (12497 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597303570 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597303570 : ℝ) + 3.141593 * 0.053049440854 / (12497 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001208091449 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049440854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403596773) : PiBarMP 12497 12 0.011 xi bn ≤ 0.162569196689 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12497 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037464606938 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.173436575469 : ℝ) ≤ √((12497 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.789981662043 : ℝ) ≤ √(12497 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12497) ≤ 0.124630204386 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037464606938 + 0.053049440854 * 1.772454 / (2 * (111.173436575469 : ℝ))) * (1 + 0.001208091449) +
        8 / (12497 * 111.789981662043) + 0.124630204386 := by gcongr
    _ ≤ (0.162569196689 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049440854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403596773) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283238153777) :
    parallelOracle 12497 0.011 xi bn cd ≤ 0.163576812437 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12497 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12497 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494238905 : ℝ) ≤ plow 12497 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.789981662043 : ℝ) ≤ √(12497 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283238153777 : ℝ) / (2 * 0.560494238905 * 111.789981662043)) * 0.162569196689 +
        0.283238153777 ^ 2 / (2 * 0.560494238905 * 111.789981662043) := by gcongr
    _ ≤ (0.163576812437 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049440854) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403596773)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283238153777) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12497 12497 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494238905 : ℝ) ≤ plow 12497 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.789981662043 : ℝ) ≤ √(12497 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12497 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12497 Θ 1.22 ≤ 0.011862427029 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.789981662043 := by gcongr <;> linarith
      _ ≤ (0.011862427029 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12497 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12497 12497 0.011 ≤ 0.008550740188 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12497 12497 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12497 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12497 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12497 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12497 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163576812437 + 0.011862427029 + (0.008550740188 : ℝ) *
        (1 + 2 * (0.283238153777 + 0.011862427029) / (0.560494238905 * 111.789981662043))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12497]

end BstLean.Part269.N12497

/-! The original eight local profiles supply actual 12497 moment certificates. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12497 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053049440854 ∧
    0 ≤ bN 12497 BstLean.Part154.csC (groupTheta g) ∧ bN 12497 BstLean.Part154.csC (groupTheta g) ≤ 0.001403596773 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12497 12497 0.011
      (momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12497 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12497 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12497 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230324642308 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12497 0.011
      (momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12497 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12497
/-! The actual computed-centre upper energy formula at 12497. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12497

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12497)
open BstLean.Part268 (cell12497)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086106234809
  | 2 => 0.087060863537
  | 3 => 0.088015453963
  | 4 => 0.088971837071
  | 5 => 0.089932212718
  | 6 => 0.090899202456
  | 7 => 0.091875906971
  | 8 => 0.092865968122
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12497 12497 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12497 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12497

/-! Actual upper energy certificates on all 43 source endpoints at 12497. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12497)
open BstLean.Part268 (cell12497)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12497 (gMinus 12497) (1 - (cell12497 i).lower) ≤ 1 ∧
    energyUpper 12497 (gMinus 12497) (BstLean.Part211.gPlus 12497)
      (finiteEnergy 12497 12497 0.011) (1 - (cell12497 i).lower) ≤
      (cell12497 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨10,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨11,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨12,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨13,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨14,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨15,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨16,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨17,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨18,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨19,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨20,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨21,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨22,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨23,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨24,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨25,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨26,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨27,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨28,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨29,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨30,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨31,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨32,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨33,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨34,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨35,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨36,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨37,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨38,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨39,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨40,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨41,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨42,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨43,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨44,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨45,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨46,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨47,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨48,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨49,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨50,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨51,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12497) (by norm_num)
        (q := 1 - (cell12497 ⟨52,by decide⟩).lower)
        (by norm_num [cell12497]) (by norm_num [cell12497])
      exact ⟨E.1,E.2.trans (by norm_num [cell12497])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12497

/-! Source-cell containment and simple scalar guards at 12497. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12497)
open BstLean.Part268 (cell12497)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12497 ⟨10,by decide⟩).lower ∧ (cell12497 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12497 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12497 ⟨11,by decide⟩).lower ∧ (cell12497 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12497 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12497 ⟨12,by decide⟩).lower ∧ (cell12497 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12497 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12497 ⟨13,by decide⟩).lower ∧ (cell12497 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12497 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12497 ⟨14,by decide⟩).lower ∧ (cell12497 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12497 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12497 ⟨15,by decide⟩).lower ∧ (cell12497 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12497 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12497 ⟨16,by decide⟩).lower ∧ (cell12497 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12497 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12497 ⟨17,by decide⟩).lower ∧ (cell12497 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12497 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12497 ⟨18,by decide⟩).lower ∧ (cell12497 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12497 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12497 ⟨19,by decide⟩).lower ∧ (cell12497 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12497 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12497 ⟨20,by decide⟩).lower ∧ (cell12497 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12497 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12497 ⟨21,by decide⟩).lower ∧ (cell12497 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12497 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12497 ⟨22,by decide⟩).lower ∧ (cell12497 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12497 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12497 ⟨23,by decide⟩).lower ∧ (cell12497 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12497 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12497 ⟨24,by decide⟩).lower ∧ (cell12497 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12497 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12497 ⟨25,by decide⟩).lower ∧ (cell12497 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12497 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12497 ⟨26,by decide⟩).lower ∧ (cell12497 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12497 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12497 ⟨27,by decide⟩).lower ∧ (cell12497 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12497 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12497 ⟨28,by decide⟩).lower ∧ (cell12497 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12497 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12497 ⟨29,by decide⟩).lower ∧ (cell12497 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12497 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12497 ⟨30,by decide⟩).lower ∧ (cell12497 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12497 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12497 ⟨31,by decide⟩).lower ∧ (cell12497 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12497 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12497 ⟨32,by decide⟩).lower ∧ (cell12497 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12497 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12497 ⟨33,by decide⟩).lower ∧ (cell12497 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12497 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12497 ⟨34,by decide⟩).lower ∧ (cell12497 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12497 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12497 ⟨35,by decide⟩).lower ∧ (cell12497 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12497 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12497 ⟨36,by decide⟩).lower ∧ (cell12497 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12497 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12497 ⟨37,by decide⟩).lower ∧ (cell12497 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12497 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12497 ⟨38,by decide⟩).lower ∧ (cell12497 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12497 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12497 ⟨39,by decide⟩).lower ∧ (cell12497 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12497 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12497 ⟨40,by decide⟩).lower ∧ (cell12497 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12497 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12497 ⟨41,by decide⟩).lower ∧ (cell12497 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12497 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12497 ⟨42,by decide⟩).lower ∧ (cell12497 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12497 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12497 ⟨43,by decide⟩).lower ∧ (cell12497 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12497 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12497 ⟨44,by decide⟩).lower ∧ (cell12497 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12497 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12497 ⟨45,by decide⟩).lower ∧ (cell12497 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12497 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12497 ⟨46,by decide⟩).lower ∧ (cell12497 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12497 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12497 ⟨47,by decide⟩).lower ∧ (cell12497 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12497 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12497 ⟨48,by decide⟩).lower ∧ (cell12497 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12497 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12497 ⟨49,by decide⟩).lower ∧ (cell12497 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12497 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12497 ⟨50,by decide⟩).lower ∧ (cell12497 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12497 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12497 ⟨51,by decide⟩).lower ∧ (cell12497 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12497 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12497 ⟨52,by decide⟩).lower ∧ (cell12497 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12497 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12497 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12497 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12497,cell12497,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12497 i).lower ∧
    (cell12497 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12497 i).upper ≤ (0.532 : ℝ) ∧
    (cell12497 i).centre ≤ (0.1 : ℝ) ∧ (cell12497 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12497 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12497 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12497

/-! The local source numeric instances at 12497 have no network premises. -/
namespace BstLean.Part269.N12497
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12497)
open BstLean.Part268 (cell12497)

noncomputable def sourceNumerics12497 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12497 (cell12497 i)
      scalarRow12497.M scalarRow12497.H scalarRow12497.xi := by
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
    energy_allowance := scalarRow12497.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12497]
    centre_nonneg := (scalarRow12497.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12497])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12497
/-! Actual 12498 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12498 ≤ (1.036100001359 : ℝ) := by
  have hr : (111.794454245279 : ℝ) ≤ √(12498 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.794454245279 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12498 12498 (11 / 1000) ≤
    (0.008550398094 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12498) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.794454245279 : ℝ) ≤ √(12498 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12498)
  have hdiv : K / √(12498 : ℝ) ≤ K / 111.794454245279 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.794454245279 ≤ (0.008550398094 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12498.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12498 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12498 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12498 := gPlus_lower 12498
end BstLean.Part269.N12498

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12498
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036100001358 : ℝ) ≤ wn 12498 := by
  have hn : √(12498 : ℝ) ≤ 111.794454245280 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12498 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.794454245280 ≤ 2 / √(12498 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256023768 : ℝ) ≤ rhoBar 12498 BstLean.Part154.csC ∧
    rhoBar 12498 BstLean.Part154.csC ≤ 0.000256024164 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036100001358 : ℝ) / (1.295212 * 12498) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036100001359 : ℝ) / (1.29521 * 12498) := by gcongr
      _ ≤ (0.000256024164 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12498 BstLean.Part154.csC) ≤ 0.001024162205 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12498 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) ≤ 0.000195553133 ∧
    cc1 (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) ≤ 0.000124431726 ∧
    cc2 (rhoBar 12498 BstLean.Part154.csC) ≤ 0.000072233533 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12498 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12498 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12498 BstLean.Part154.csC * nuR (rhoBar 12498 BstLean.Part154.csC)) ≤ 0.000512064715 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256024164 : ℝ) * 0.001024162205 := by gcongr
      _ ≤ (0.000512064715 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12498 BstLean.Part154.csC) * nuR (rhoBar 12498 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024162205 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12498 BstLean.Part154.csC) * rhoBar 12498 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256024164 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256024164 / 2 + 0.399 * 0.001024162205 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195553133 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512064715 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124431726 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256024164 / 1.414213562 := by gcongr
      _ ≤ (0.000072233533 : ℝ) := by norm_num

end BstLean.Part269.N12498

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12498
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) ≤ 1.65145E-7 := by
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12498 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12498 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12498 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195553133 : ℝ) ^ 2 + 0.000124431726 ^ 2 + 3 * 0.000072233533 ^ 2 +
        2 * 0.797885 * 0.000195553133 * 0.000124431726 + 2 * 0.000195553133 * 0.000072233533 +
        4 * 0.797885 * 0.000124431726 * 0.000072233533 := by gcongr
    _ ≤ (1.65145E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12498 BstLean.Part154.csC Θ ≤ 0.002673294532 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12498 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12498 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12498 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036100001359 * 1.65145E-7 / (0.000256023768 : ℝ) := by gcongr
    _ ≤ 0.002673294532 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12498 BstLean.Part154.csC Θ ≤ 0.002966990147 + 0.000675496084 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12498 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12498 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036100001359 : ℝ) * ((2 * Θ * 0.000256024164 +
        (6863 / 10000) * 0.000256024164 * 12498 * 0.001024162205) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002966990147 + 0.000675496084 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12498 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12498 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12498 0.011 Θ ∧ gammaRatio 12498 0.011 Θ ≤ 0.000088014487 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12498 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036100001359 : ℝ) * 0.525 / ((1 - 0.011) * 12498) := by gcongr
      _ ≤ (0.000088014487 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12498 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12498 0.011 Θ) :=
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
    badAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12498 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12498 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12498 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12498 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12498 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12498 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12498 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12498 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12498 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12498 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036100001359 : ℝ) * 12498 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003784329309 + 0.003348790616 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12498

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12498
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12498 BstLean.Part154.csC) (piBar (rhoBar 12498 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12498 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12498 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12498 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12498 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12498 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12498 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12498 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12498 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12498 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12498 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052911371408 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12498) ≤ 0.010682440280 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12498 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036100001359)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010682440280 + 2 * 0.737676 / 12498) := by gcongr
    _ ≤ (0.052911371408 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12498 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12498

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12498
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494285605 : ℝ) ≤ plow 12498 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12498) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049044383)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403479630) : eMP 12498 0.011 xi bn ≤ 0.001207992627 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12498 : ℝ) * (1 - 0.011))) ≤ 0.000597254749 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403479630 / (12498 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597254749 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597254749 : ℝ) + 3.141593 * 0.053049044383 / (12498 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207992627 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049044383)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403479630) : PiBarMP 12498 12 0.011 xi bn ≤ 0.162562620745 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12498 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037463043523 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.177884491476 : ℝ) ≤ √((12498 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.794454245279 : ℝ) ≤ √(12498 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12498) ≤ 0.124625218280 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037463043523 + 0.053049044383 * 1.772454 / (2 * (111.177884491476 : ℝ))) * (1 + 0.001207992627) +
        8 / (12498 * 111.794454245279) + 0.124625218280 := by gcongr
    _ ≤ (0.162562620745 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049044383)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403479630) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283235153036) :
    parallelOracle 12498 0.011 xi bn cd ≤ 0.163570163778 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12498 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12498 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494285605 : ℝ) ≤ plow 12498 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.794454245279 : ℝ) ≤ √(12498 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283235153036 : ℝ) / (2 * 0.560494285605 * 111.794454245279)) * 0.162562620745 +
        0.283235153036 ^ 2 / (2 * 0.560494285605 * 111.794454245279) := by gcongr
    _ ≤ (0.163570163778 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053049044383) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403479630)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283235153036) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12498 12498 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494285605 : ℝ) ≤ plow 12498 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.794454245279 : ℝ) ≤ √(12498 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12498 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12498 Θ 1.22 ≤ 0.011861952447 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.794454245279 := by gcongr <;> linarith
      _ ≤ (0.011861952447 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12498 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12498 12498 0.011 ≤ 0.008550398094 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12498 12498 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12498 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12498 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12498 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12498 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163570163778 + 0.011861952447 + (0.008550398094 : ℝ) *
        (1 + 2 * (0.283235153036 + 0.011861952447) / (0.560494285605 * 111.794454245279))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12498]

end BstLean.Part269.N12498

/-! The original eight local profiles supply actual 12498 moment certificates. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12498 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053049044383 ∧
    0 ≤ bN 12498 BstLean.Part154.csC (groupTheta g) ∧ bN 12498 BstLean.Part154.csC (groupTheta g) ≤ 0.001403479630 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12498 12498 0.011
      (momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12498 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12498 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12498 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230323781628 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12498 0.011
      (momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12498 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12498
/-! The actual computed-centre upper energy formula at 12498. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12498

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12498)
open BstLean.Part268 (cell12498)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086103074404
  | 2 => 0.087057639245
  | 3 => 0.088012155550
  | 4 => 0.088968452020
  | 5 => 0.089928725835
  | 6 => 0.090895595433
  | 7 => 0.091872157905
  | 8 => 0.092862050974
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12498 12498 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12498 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12498

/-! Actual upper energy certificates on all 43 source endpoints at 12498. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12498)
open BstLean.Part268 (cell12498)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12498 (gMinus 12498) (1 - (cell12498 i).lower) ≤ 1 ∧
    energyUpper 12498 (gMinus 12498) (BstLean.Part211.gPlus 12498)
      (finiteEnergy 12498 12498 0.011) (1 - (cell12498 i).lower) ≤
      (cell12498 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨10,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨11,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨12,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨13,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨14,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨15,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨16,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨17,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨18,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨19,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨20,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨21,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨22,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨23,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨24,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨25,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨26,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨27,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨28,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨29,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨30,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨31,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨32,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨33,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨34,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨35,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨36,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨37,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨38,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨39,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨40,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨41,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨42,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨43,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨44,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨45,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨46,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨47,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨48,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨49,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨50,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨51,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12498) (by norm_num)
        (q := 1 - (cell12498 ⟨52,by decide⟩).lower)
        (by norm_num [cell12498]) (by norm_num [cell12498])
      exact ⟨E.1,E.2.trans (by norm_num [cell12498])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12498

/-! Source-cell containment and simple scalar guards at 12498. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12498)
open BstLean.Part268 (cell12498)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12498 ⟨10,by decide⟩).lower ∧ (cell12498 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12498 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12498 ⟨11,by decide⟩).lower ∧ (cell12498 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12498 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12498 ⟨12,by decide⟩).lower ∧ (cell12498 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12498 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12498 ⟨13,by decide⟩).lower ∧ (cell12498 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12498 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12498 ⟨14,by decide⟩).lower ∧ (cell12498 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12498 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12498 ⟨15,by decide⟩).lower ∧ (cell12498 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12498 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12498 ⟨16,by decide⟩).lower ∧ (cell12498 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12498 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12498 ⟨17,by decide⟩).lower ∧ (cell12498 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12498 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12498 ⟨18,by decide⟩).lower ∧ (cell12498 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12498 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12498 ⟨19,by decide⟩).lower ∧ (cell12498 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12498 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12498 ⟨20,by decide⟩).lower ∧ (cell12498 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12498 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12498 ⟨21,by decide⟩).lower ∧ (cell12498 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12498 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12498 ⟨22,by decide⟩).lower ∧ (cell12498 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12498 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12498 ⟨23,by decide⟩).lower ∧ (cell12498 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12498 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12498 ⟨24,by decide⟩).lower ∧ (cell12498 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12498 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12498 ⟨25,by decide⟩).lower ∧ (cell12498 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12498 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12498 ⟨26,by decide⟩).lower ∧ (cell12498 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12498 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12498 ⟨27,by decide⟩).lower ∧ (cell12498 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12498 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12498 ⟨28,by decide⟩).lower ∧ (cell12498 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12498 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12498 ⟨29,by decide⟩).lower ∧ (cell12498 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12498 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12498 ⟨30,by decide⟩).lower ∧ (cell12498 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12498 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12498 ⟨31,by decide⟩).lower ∧ (cell12498 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12498 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12498 ⟨32,by decide⟩).lower ∧ (cell12498 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12498 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12498 ⟨33,by decide⟩).lower ∧ (cell12498 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12498 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12498 ⟨34,by decide⟩).lower ∧ (cell12498 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12498 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12498 ⟨35,by decide⟩).lower ∧ (cell12498 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12498 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12498 ⟨36,by decide⟩).lower ∧ (cell12498 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12498 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12498 ⟨37,by decide⟩).lower ∧ (cell12498 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12498 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12498 ⟨38,by decide⟩).lower ∧ (cell12498 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12498 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12498 ⟨39,by decide⟩).lower ∧ (cell12498 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12498 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12498 ⟨40,by decide⟩).lower ∧ (cell12498 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12498 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12498 ⟨41,by decide⟩).lower ∧ (cell12498 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12498 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12498 ⟨42,by decide⟩).lower ∧ (cell12498 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12498 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12498 ⟨43,by decide⟩).lower ∧ (cell12498 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12498 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12498 ⟨44,by decide⟩).lower ∧ (cell12498 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12498 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12498 ⟨45,by decide⟩).lower ∧ (cell12498 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12498 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12498 ⟨46,by decide⟩).lower ∧ (cell12498 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12498 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12498 ⟨47,by decide⟩).lower ∧ (cell12498 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12498 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12498 ⟨48,by decide⟩).lower ∧ (cell12498 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12498 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12498 ⟨49,by decide⟩).lower ∧ (cell12498 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12498 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12498 ⟨50,by decide⟩).lower ∧ (cell12498 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12498 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12498 ⟨51,by decide⟩).lower ∧ (cell12498 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12498 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12498 ⟨52,by decide⟩).lower ∧ (cell12498 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12498 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12498 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12498 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12498,cell12498,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12498 i).lower ∧
    (cell12498 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12498 i).upper ≤ (0.532 : ℝ) ∧
    (cell12498 i).centre ≤ (0.1 : ℝ) ∧ (cell12498 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12498 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12498 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12498

/-! The local source numeric instances at 12498 have no network premises. -/
namespace BstLean.Part269.N12498
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12498)
open BstLean.Part268 (cell12498)

noncomputable def sourceNumerics12498 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12498 (cell12498 i)
      scalarRow12498.M scalarRow12498.H scalarRow12498.xi := by
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
    energy_allowance := scalarRow12498.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12498]
    centre_nonneg := (scalarRow12498.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12498])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12498
/-! Actual 12499 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12499 ≤ (1.036098544412 : ℝ) := by
  have hr : (111.798926649588 : ℝ) ≤ √(12499 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.798926649588 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12499 12499 (11 / 1000) ≤
    (0.008550056041 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12499) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.798926649588 : ℝ) ≤ √(12499 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12499)
  have hdiv : K / √(12499 : ℝ) ≤ K / 111.798926649588 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.798926649588 ≤ (0.008550056041 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12499.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12499 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12499 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12499 := gPlus_lower 12499
end BstLean.Part269.N12499

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12499
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036098544411 : ℝ) ≤ wn 12499 := by
  have hn : √(12499 : ℝ) ≤ 111.798926649589 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12499 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.798926649589 ≤ 2 / √(12499 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256002924 : ℝ) ≤ rhoBar 12499 BstLean.Part154.csC ∧
    rhoBar 12499 BstLean.Part154.csC ≤ 0.000256003321 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036098544411 : ℝ) / (1.295212 * 12499) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036098544412 : ℝ) / (1.29521 * 12499) := by gcongr
      _ ≤ (0.000256003321 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12499 BstLean.Part154.csC) ≤ 0.001024078822 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12499 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) ≤ 0.000195537212 ∧
    cc1 (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) ≤ 0.000124421596 ∧
    cc2 (rhoBar 12499 BstLean.Part154.csC) ≤ 0.000072227653 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12499 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12499 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12499 BstLean.Part154.csC * nuR (rhoBar 12499 BstLean.Part154.csC)) ≤ 0.000512023027 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256003321 : ℝ) * 0.001024078822 := by gcongr
      _ ≤ (0.000512023027 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12499 BstLean.Part154.csC) * nuR (rhoBar 12499 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001024078822 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12499 BstLean.Part154.csC) * rhoBar 12499 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256003321 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256003321 / 2 + 0.399 * 0.001024078822 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195537212 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512023027 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124421596 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256003321 / 1.414213562 := by gcongr
      _ ≤ (0.000072227653 : ℝ) := by norm_num

end BstLean.Part269.N12499

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12499
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) ≤ 1.65118E-7 := by
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12499 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12499 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12499 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195537212 : ℝ) ^ 2 + 0.000124421596 ^ 2 + 3 * 0.000072227653 ^ 2 +
        2 * 0.797885 * 0.000195537212 * 0.000124421596 + 2 * 0.000195537212 * 0.000072227653 +
        4 * 0.797885 * 0.000124421596 * 0.000072227653 := by gcongr
    _ ≤ (1.65118E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12499 BstLean.Part154.csC Θ ≤ 0.002673071336 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12499 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12499 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12499 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036098544412 * 1.65118E-7 / (0.000256002924 : ℝ) := by gcongr
    _ ≤ 0.002673071336 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12499 BstLean.Part154.csC Θ ≤ 0.002966740250 + 0.000675440142 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12499 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12499 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036098544412 : ℝ) * ((2 * Θ * 0.000256003321 +
        (6863 / 10000) * 0.000256003321 * 12499 * 0.001024078822) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002966740250 + 0.000675440142 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12499 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12499 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12499 0.011 Θ ∧ gammaRatio 12499 0.011 Θ ≤ 0.000088007322 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12499 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036098544412 : ℝ) * 0.525 / ((1 - 0.011) * 12499) := by gcongr
      _ ≤ (0.000088007322 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12499 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12499 0.011 Θ) :=
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
    badAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12499 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12499 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12499 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12499 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12499 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12499 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12499 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12499 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12499 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12499 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036098544412 : ℝ) * 12499 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003784079412 + 0.003348511478 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12499

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12499
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12499 BstLean.Part154.csC) (piBar (rhoBar 12499 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12499 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12499 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12499 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12499 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12499 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12499 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12499 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12499 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12499 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12499 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052909231610 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12499) ≤ 0.010682012940 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12499 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036098544412)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010682012940 + 2 * 0.737676 / 12499) := by gcongr
    _ ≤ (0.052909231610 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12499 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12499

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12499
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494332298 : ℝ) ≤ plow 12499 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12499) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053048647938)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403362452) : eMP 12499 0.011 xi bn ≤ 0.001207893798 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12499 : ℝ) * (1 - 0.011))) ≤ 0.000597205924 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403362452 / (12499 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597205924 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597205924 : ℝ) + 3.141593 * 0.053048647938 / (12499 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207893798 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053048647938)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403362452) : PiBarMP 12499 12 0.011 xi bn ≤ 0.162556044870 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12499 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037461479576 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.182332229540 : ℝ) ≤ √((12499 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.798926649588 : ℝ) ≤ √(12499 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12499) ≤ 0.124620232773 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037461479576 + 0.053048647938 * 1.772454 / (2 * (111.182332229540 : ℝ))) * (1 + 0.001207893798) +
        8 / (12499 * 111.798926649588) + 0.124620232773 := by gcongr
    _ ≤ (0.162556044870 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053048647938)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403362452) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283232152611) :
    parallelOracle 12499 0.011 xi bn cd ≤ 0.163563515198 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12499 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12499 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494332298 : ℝ) ≤ plow 12499 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.798926649588 : ℝ) ≤ √(12499 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283232152611 : ℝ) / (2 * 0.560494332298 * 111.798926649588)) * 0.162556044870 +
        0.283232152611 ^ 2 / (2 * 0.560494332298 * 111.798926649588) := by gcongr
    _ ≤ (0.163563515198 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053048647938) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403362452)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283232152611) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12499 12499 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494332298 : ℝ) ≤ plow 12499 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.798926649588 : ℝ) ≤ √(12499 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12499 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12499 Θ 1.22 ≤ 0.011861477921 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.798926649588 := by gcongr <;> linarith
      _ ≤ (0.011861477921 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12499 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12499 12499 0.011 ≤ 0.008550056041 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12499 12499 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12499 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12499 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12499 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12499 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163563515198 + 0.011861477921 + (0.008550056041 : ℝ) *
        (1 + 2 * (0.283232152611 + 0.011861477921) / (0.560494332298 * 111.798926649588))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12499]

end BstLean.Part269.N12499

/-! The original eight local profiles supply actual 12499 moment certificates. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12499 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053048647938 ∧
    0 ≤ bN 12499 BstLean.Part154.csC (groupTheta g) ∧ bN 12499 BstLean.Part154.csC (groupTheta g) ≤ 0.001403362452 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12499 12499 0.011
      (momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12499 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12499 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12499 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230322921001 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12499 0.011
      (momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12499 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12499
/-! The actual computed-centre upper energy formula at 12499. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12499

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12499)
open BstLean.Part268 (cell12499)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086099915337
  | 2 => 0.087054416349
  | 3 => 0.088008858605
  | 4 => 0.088965068524
  | 5 => 0.089925240613
  | 6 => 0.090891990202
  | 7 => 0.091868410786
  | 8 => 0.092858135960
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12499 12499 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12499 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12499

/-! Actual upper energy certificates on all 43 source endpoints at 12499. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12499)
open BstLean.Part268 (cell12499)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12499 (gMinus 12499) (1 - (cell12499 i).lower) ≤ 1 ∧
    energyUpper 12499 (gMinus 12499) (BstLean.Part211.gPlus 12499)
      (finiteEnergy 12499 12499 0.011) (1 - (cell12499 i).lower) ≤
      (cell12499 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨10,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨11,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨12,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨13,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨14,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨15,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨16,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨17,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨18,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨19,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨20,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨21,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨22,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨23,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨24,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨25,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨26,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨27,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨28,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨29,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨30,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨31,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨32,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨33,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨34,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨35,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨36,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨37,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨38,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨39,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨40,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨41,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨42,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨43,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨44,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨45,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨46,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨47,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨48,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨49,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨50,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨51,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12499) (by norm_num)
        (q := 1 - (cell12499 ⟨52,by decide⟩).lower)
        (by norm_num [cell12499]) (by norm_num [cell12499])
      exact ⟨E.1,E.2.trans (by norm_num [cell12499])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12499

/-! Source-cell containment and simple scalar guards at 12499. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12499)
open BstLean.Part268 (cell12499)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12499 ⟨10,by decide⟩).lower ∧ (cell12499 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12499 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12499 ⟨11,by decide⟩).lower ∧ (cell12499 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12499 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12499 ⟨12,by decide⟩).lower ∧ (cell12499 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12499 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12499 ⟨13,by decide⟩).lower ∧ (cell12499 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12499 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12499 ⟨14,by decide⟩).lower ∧ (cell12499 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12499 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12499 ⟨15,by decide⟩).lower ∧ (cell12499 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12499 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12499 ⟨16,by decide⟩).lower ∧ (cell12499 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12499 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12499 ⟨17,by decide⟩).lower ∧ (cell12499 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12499 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12499 ⟨18,by decide⟩).lower ∧ (cell12499 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12499 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12499 ⟨19,by decide⟩).lower ∧ (cell12499 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12499 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12499 ⟨20,by decide⟩).lower ∧ (cell12499 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12499 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12499 ⟨21,by decide⟩).lower ∧ (cell12499 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12499 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12499 ⟨22,by decide⟩).lower ∧ (cell12499 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12499 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12499 ⟨23,by decide⟩).lower ∧ (cell12499 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12499 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12499 ⟨24,by decide⟩).lower ∧ (cell12499 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12499 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12499 ⟨25,by decide⟩).lower ∧ (cell12499 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12499 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12499 ⟨26,by decide⟩).lower ∧ (cell12499 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12499 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12499 ⟨27,by decide⟩).lower ∧ (cell12499 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12499 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12499 ⟨28,by decide⟩).lower ∧ (cell12499 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12499 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12499 ⟨29,by decide⟩).lower ∧ (cell12499 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12499 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12499 ⟨30,by decide⟩).lower ∧ (cell12499 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12499 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12499 ⟨31,by decide⟩).lower ∧ (cell12499 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12499 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12499 ⟨32,by decide⟩).lower ∧ (cell12499 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12499 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12499 ⟨33,by decide⟩).lower ∧ (cell12499 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12499 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12499 ⟨34,by decide⟩).lower ∧ (cell12499 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12499 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12499 ⟨35,by decide⟩).lower ∧ (cell12499 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12499 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12499 ⟨36,by decide⟩).lower ∧ (cell12499 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12499 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12499 ⟨37,by decide⟩).lower ∧ (cell12499 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12499 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12499 ⟨38,by decide⟩).lower ∧ (cell12499 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12499 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12499 ⟨39,by decide⟩).lower ∧ (cell12499 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12499 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12499 ⟨40,by decide⟩).lower ∧ (cell12499 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12499 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12499 ⟨41,by decide⟩).lower ∧ (cell12499 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12499 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12499 ⟨42,by decide⟩).lower ∧ (cell12499 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12499 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12499 ⟨43,by decide⟩).lower ∧ (cell12499 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12499 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12499 ⟨44,by decide⟩).lower ∧ (cell12499 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12499 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12499 ⟨45,by decide⟩).lower ∧ (cell12499 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12499 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12499 ⟨46,by decide⟩).lower ∧ (cell12499 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12499 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12499 ⟨47,by decide⟩).lower ∧ (cell12499 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12499 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12499 ⟨48,by decide⟩).lower ∧ (cell12499 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12499 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12499 ⟨49,by decide⟩).lower ∧ (cell12499 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12499 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12499 ⟨50,by decide⟩).lower ∧ (cell12499 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12499 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12499 ⟨51,by decide⟩).lower ∧ (cell12499 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12499 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12499 ⟨52,by decide⟩).lower ∧ (cell12499 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12499 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12499 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12499 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12499,cell12499,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12499 i).lower ∧
    (cell12499 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12499 i).upper ≤ (0.532 : ℝ) ∧
    (cell12499 i).centre ≤ (0.1 : ℝ) ∧ (cell12499 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12499 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12499 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12499

/-! The local source numeric instances at 12499 have no network premises. -/
namespace BstLean.Part269.N12499
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12499)
open BstLean.Part268 (cell12499)

noncomputable def sourceNumerics12499 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12499 (cell12499 i)
      scalarRow12499.M scalarRow12499.H scalarRow12499.xi := by
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
    energy_allowance := scalarRow12499.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12499]
    centre_nonneg := (scalarRow12499.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12499])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12499