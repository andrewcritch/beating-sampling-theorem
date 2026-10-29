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
import BstLean.Part269Direction34
import BstLean.Part269Shared34
import BstLean.Part269Finite
import BstLean.Part269N13224Source
import BstLean.Part269Rows34
import BstLean.Part269Source
/-! Actual 13200 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13200 ≤ (1.035118561495 : ℝ) := by
  have hr : (114.891252930760 : ℝ) ≤ √(13200 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.891252930760 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13200 13200 (11 / 1000) ≤
    (0.008319927458 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13200) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.891252930760 : ℝ) ≤ √(13200 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13200)
  have hdiv : K / √(13200 : ℝ) ≤ K / 114.891252930760 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.891252930760 ≤ (0.008319927458 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13200.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13200 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13200 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13200 := gPlus_lower 13200
end BstLean.Part269.N13200

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13200
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035118561494 : ℝ) ≤ wn 13200 := by
  have hn : √(13200 : ℝ) ≤ 114.891252930761 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13200 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.891252930761 ≤ 2 / √(13200 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242178339 : ℝ) ≤ rhoBar 13200 BstLean.Part154.csC ∧
    rhoBar 13200 BstLean.Part154.csC ≤ 0.000242178714 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035118561494 : ℝ) / (1.295212 * 13200) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035118561495 : ℝ) / (1.29521 * 13200) := by gcongr
      _ ≤ (0.000242178714 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13200 BstLean.Part154.csC) ≤ 0.000968773507 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13200 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) ≤ 0.000184977404 ∧
    cc1 (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) ≤ 0.000117702419 ∧
    cc2 (rhoBar 13200 BstLean.Part154.csC) ≤ 0.000068327239 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13200 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13200 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13200 BstLean.Part154.csC * nuR (rhoBar 13200 BstLean.Part154.csC)) ≤ 0.000484372091 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242178714 : ℝ) * 0.000968773507 := by gcongr
      _ ≤ (0.000484372091 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13200 BstLean.Part154.csC) * nuR (rhoBar 13200 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968773507 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13200 BstLean.Part154.csC) * rhoBar 13200 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242178714 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242178714 / 2 + 0.399 * 0.000968773507 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184977404 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484372091 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117702419 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242178714 / 1.414213562 := by gcongr
      _ ≤ (0.000068327239 : ℝ) := by norm_num

end BstLean.Part269.N13200

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13200
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) ≤ 1.47766E-7 := by
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13200 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13200 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13200 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184977404 : ℝ) ^ 2 + 0.000117702419 ^ 2 + 3 * 0.000068327239 ^ 2 +
        2 * 0.797885 * 0.000184977404 * 0.000117702419 + 2 * 0.000184977404 * 0.000068327239 +
        4 * 0.797885 * 0.000117702419 * 0.000068327239 := by gcongr
    _ ≤ (1.47766E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13200 BstLean.Part154.csC Θ ≤ 0.002526325517 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13200 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13200 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13200 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035118561495 * 1.47766E-7 / (0.000242178339 : ℝ) := by gcongr
    _ ≤ 0.002526325517 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13200 BstLean.Part154.csC Θ ≤ 0.002801215094 + 0.000638360888 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13200 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13200 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035118561495 : ℝ) * ((2 * Θ * 0.000242178714 +
        (6863 / 10000) * 0.000242178714 * 13200 * 0.000968773507) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002801215094 + 0.000638360888 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13200 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13200 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13200 0.011 Θ ∧ gammaRatio 13200 0.011 Θ ≤ 0.000083254780 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13200 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035118561495 : ℝ) * 0.525 / ((1 - 0.011) * 13200) := by gcongr
      _ ≤ (0.000083254780 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13200 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13200 0.011 Θ) :=
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
    badAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13200 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13200 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13200 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13200 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13200 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13200 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13200 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13200 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13200 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13200 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035118561495 : ℝ) * 13200 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003118785860 + 0.003164686405 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13200

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13200
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13200 BstLean.Part154.csC) (piBar (rhoBar 13200 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13200 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13200 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13200 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13200 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13200 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13200 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13200 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13200 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13200 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13200 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051470021449 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13200) ≤ 0.010394503939 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13200 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035118561495)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010394503939 + 2 * 0.737676 / 13200) := by gcongr
    _ ≤ (0.051470021449 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13200 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13200

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13200
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525323280 : ℝ) ≤ plow 13200 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13200) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286846223)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326320897) : eMP 13200 0.011 xi bn ≤ 0.001142493429 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13200 : ℝ) * (1 - 0.011))) ≤ 0.000564955389 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326320897 / (13200 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564955389 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564955389 : ℝ) + 3.141593 * 0.052286846223 / (13200 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142493429 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286846223)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326320897) : PiBarMP 13200 12 0.011 xi bn ≤ 0.158137641377 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13200 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036418688843 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.257603685706 : ℝ) ≤ √((13200 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.891252930760 : ℝ) ≤ √(13200 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13200) ≤ 0.121266048610 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036418688843 + 0.052286846223 * 1.772454 / (2 * (114.257603685706 : ℝ))) * (1 + 0.001142493429) +
        8 / (13200 * 114.891252930760) + 0.121266048610 := by gcongr
    _ ≤ (0.158137641377 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286846223)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326320897) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280133193436) :
    parallelOracle 13200 0.011 xi bn cd ≤ 0.159090865324 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13200 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13200 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525323280 : ℝ) ≤ plow 13200 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.891252930760 : ℝ) ≤ √(13200 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280133193436 : ℝ) / (2 * 0.560525323280 * 114.891252930760)) * 0.158137641377 +
        0.280133193436 ^ 2 / (2 * 0.560525323280 * 114.891252930760) := by gcongr
    _ ≤ (0.159090865324 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286846223) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326320897)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280133193436) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13200 13200 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525323280 : ℝ) ≤ plow 13200 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.891252930760 : ℝ) ≤ √(13200 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13200 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13200 Θ 1.22 ≤ 0.011542223331 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.891252930760 := by gcongr <;> linarith
      _ ≤ (0.011542223331 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13200 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13200 13200 0.011 ≤ 0.008319927458 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13200 13200 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13200 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13200 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13200 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13200 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159090865324 + 0.011542223331 + (0.008319927458 : ℝ) *
        (1 + 2 * (0.280133193436 + 0.011542223331) / (0.560525323280 * 114.891252930760))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13200]

end BstLean.Part269.N13200

/-! The original eight local profiles supply actual 13200 moment certificates. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13200 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052286846223 ∧
    0 ≤ bN 13200 BstLean.Part154.csC (groupTheta g) ∧ bN 13200 BstLean.Part154.csC (groupTheta g) ≤ 0.001326320897 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13200 13200 0.011
      (momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13200 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13200 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13200 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228663171987 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13200 0.011
      (momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13200 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13200
/-! The actual computed-centre upper energy formula at 13200. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13200

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13200)
open BstLean.Part268 (cell13200)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084151608095
  | 2 => 0.085073893735
  | 3 => 0.085991463066
  | 4 => 0.086905060664
  | 5 => 0.087815605860
  | 6 => 0.088724220945
  | 7 => 0.089632262469
  | 8 => 0.090541355753
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13200 13200 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13200 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13200

/-! Actual upper energy certificates on all 43 source endpoints at 13200. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13200)
open BstLean.Part268 (cell13200)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13200 (gMinus 13200) (1 - (cell13200 i).lower) ≤ 1 ∧
    energyUpper 13200 (gMinus 13200) (BstLean.Part211.gPlus 13200)
      (finiteEnergy 13200 13200 0.011) (1 - (cell13200 i).lower) ≤
      (cell13200 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨10,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨11,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨12,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨13,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨14,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨15,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨16,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨17,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨18,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨19,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨20,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨21,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨22,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨23,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨24,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨25,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨26,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨27,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨28,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨29,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨30,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨31,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨32,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨33,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨34,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨35,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨36,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨37,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨38,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨39,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨40,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨41,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨42,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨43,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨44,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨45,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨46,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨47,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨48,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨49,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨50,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨51,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13200) (by norm_num)
        (q := 1 - (cell13200 ⟨52,by decide⟩).lower)
        (by norm_num [cell13200]) (by norm_num [cell13200])
      exact ⟨E.1,E.2.trans (by norm_num [cell13200])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13200

/-! Source-cell containment and simple scalar guards at 13200. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13200)
open BstLean.Part268 (cell13200)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13200 ⟨10,by decide⟩).lower ∧ (cell13200 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13200 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13200 ⟨11,by decide⟩).lower ∧ (cell13200 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13200 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13200 ⟨12,by decide⟩).lower ∧ (cell13200 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13200 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13200 ⟨13,by decide⟩).lower ∧ (cell13200 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13200 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13200 ⟨14,by decide⟩).lower ∧ (cell13200 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13200 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13200 ⟨15,by decide⟩).lower ∧ (cell13200 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13200 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13200 ⟨16,by decide⟩).lower ∧ (cell13200 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13200 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13200 ⟨17,by decide⟩).lower ∧ (cell13200 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13200 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13200 ⟨18,by decide⟩).lower ∧ (cell13200 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13200 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13200 ⟨19,by decide⟩).lower ∧ (cell13200 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13200 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13200 ⟨20,by decide⟩).lower ∧ (cell13200 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13200 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13200 ⟨21,by decide⟩).lower ∧ (cell13200 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13200 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13200 ⟨22,by decide⟩).lower ∧ (cell13200 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13200 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13200 ⟨23,by decide⟩).lower ∧ (cell13200 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13200 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13200 ⟨24,by decide⟩).lower ∧ (cell13200 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13200 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13200 ⟨25,by decide⟩).lower ∧ (cell13200 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13200 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13200 ⟨26,by decide⟩).lower ∧ (cell13200 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13200 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13200 ⟨27,by decide⟩).lower ∧ (cell13200 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13200 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13200 ⟨28,by decide⟩).lower ∧ (cell13200 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13200 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13200 ⟨29,by decide⟩).lower ∧ (cell13200 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13200 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13200 ⟨30,by decide⟩).lower ∧ (cell13200 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13200 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13200 ⟨31,by decide⟩).lower ∧ (cell13200 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13200 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13200 ⟨32,by decide⟩).lower ∧ (cell13200 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13200 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13200 ⟨33,by decide⟩).lower ∧ (cell13200 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13200 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13200 ⟨34,by decide⟩).lower ∧ (cell13200 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13200 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13200 ⟨35,by decide⟩).lower ∧ (cell13200 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13200 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13200 ⟨36,by decide⟩).lower ∧ (cell13200 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13200 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13200 ⟨37,by decide⟩).lower ∧ (cell13200 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13200 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13200 ⟨38,by decide⟩).lower ∧ (cell13200 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13200 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13200 ⟨39,by decide⟩).lower ∧ (cell13200 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13200 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13200 ⟨40,by decide⟩).lower ∧ (cell13200 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13200 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13200 ⟨41,by decide⟩).lower ∧ (cell13200 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13200 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13200 ⟨42,by decide⟩).lower ∧ (cell13200 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13200 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13200 ⟨43,by decide⟩).lower ∧ (cell13200 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13200 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13200 ⟨44,by decide⟩).lower ∧ (cell13200 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13200 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13200 ⟨45,by decide⟩).lower ∧ (cell13200 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13200 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13200 ⟨46,by decide⟩).lower ∧ (cell13200 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13200 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13200 ⟨47,by decide⟩).lower ∧ (cell13200 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13200 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13200 ⟨48,by decide⟩).lower ∧ (cell13200 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13200 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13200 ⟨49,by decide⟩).lower ∧ (cell13200 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13200 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13200 ⟨50,by decide⟩).lower ∧ (cell13200 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13200 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13200 ⟨51,by decide⟩).lower ∧ (cell13200 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13200 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13200 ⟨52,by decide⟩).lower ∧ (cell13200 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13200 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13200 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13200 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13200,cell13200,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13200 i).lower ∧
    (cell13200 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13200 i).upper ≤ (0.532 : ℝ) ∧
    (cell13200 i).centre ≤ (0.1 : ℝ) ∧ (cell13200 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13200 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13200 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13200

/-! The local source numeric instances at 13200 have no network premises. -/
namespace BstLean.Part269.N13200
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13200)
open BstLean.Part268 (cell13200)

noncomputable def sourceNumerics13200 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13200 (cell13200 i)
      scalarRow13200.M scalarRow13200.H scalarRow13200.xi := by
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
    energy_allowance := scalarRow13200.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13200]
    centre_nonneg := (scalarRow13200.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13200])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13200
/-! Actual 13201 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13201 ≤ (1.035117219844 : ℝ) := by
  have hr : (114.895604789739 : ℝ) ≤ √(13201 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.895604789739 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13201 13201 (11 / 1000) ≤
    (0.008319612325 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13201) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.895604789739 : ℝ) ≤ √(13201 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13201)
  have hdiv : K / √(13201 : ℝ) ≤ K / 114.895604789739 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.895604789739 ≤ (0.008319612325 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13201.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13201 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13201 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13201 := gPlus_lower 13201
end BstLean.Part269.N13201

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13201
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035117219843 : ℝ) ≤ wn 13201 := by
  have hn : √(13201 : ℝ) ≤ 114.895604789740 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13201 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.895604789740 ≤ 2 / √(13201 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242159680 : ℝ) ≤ rhoBar 13201 BstLean.Part154.csC ∧
    rhoBar 13201 BstLean.Part154.csC ≤ 0.000242160055 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035117219843 : ℝ) / (1.295212 * 13201) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035117219844 : ℝ) / (1.29521 * 13201) := by gcongr
      _ ≤ (0.000242160055 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13201 BstLean.Part154.csC) ≤ 0.000968698862 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13201 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) ≤ 0.000184963152 ∧
    cc1 (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) ≤ 0.000117693350 ∧
    cc2 (rhoBar 13201 BstLean.Part154.csC) ≤ 0.000068321974 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13201 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13201 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13201 BstLean.Part154.csC * nuR (rhoBar 13201 BstLean.Part154.csC)) ≤ 0.000484334771 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242160055 : ℝ) * 0.000968698862 := by gcongr
      _ ≤ (0.000484334771 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13201 BstLean.Part154.csC) * nuR (rhoBar 13201 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968698862 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13201 BstLean.Part154.csC) * rhoBar 13201 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242160055 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242160055 / 2 + 0.399 * 0.000968698862 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184963152 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484334771 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117693350 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242160055 / 1.414213562 := by gcongr
      _ ≤ (0.000068321974 : ℝ) := by norm_num

end BstLean.Part269.N13201

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13201
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) ≤ 1.47743E-7 := by
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13201 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13201 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13201 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184963152 : ℝ) ^ 2 + 0.000117693350 ^ 2 + 3 * 0.000068321974 ^ 2 +
        2 * 0.797885 * 0.000184963152 * 0.000117693350 + 2 * 0.000184963152 * 0.000068321974 +
        4 * 0.797885 * 0.000117693350 * 0.000068321974 := by gcongr
    _ ≤ (1.47743E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13201 BstLean.Part154.csC Θ ≤ 0.002526123646 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13201 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13201 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13201 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035117219844 * 1.47743E-7 / (0.000242159680 : ℝ) := by gcongr
    _ ≤ 0.002526123646 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13201 BstLean.Part154.csC Θ ≤ 0.002800992001 + 0.000638310877 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13201 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13201 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035117219844 : ℝ) * ((2 * Θ * 0.000242160055 +
        (6863 / 10000) * 0.000242160055 * 13201 * 0.000968698862) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002800992001 + 0.000638310877 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13201 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13201 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13201 0.011 Θ ∧ gammaRatio 13201 0.011 Θ ≤ 0.000083248365 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13201 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035117219844 : ℝ) * 0.525 / ((1 - 0.011) * 13201) := by gcongr
      _ ≤ (0.000083248365 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13201 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13201 0.011 Θ) :=
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
    badAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13201 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13201 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13201 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13201 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13201 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13201 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13201 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13201 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13201 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13201 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035117219844 : ℝ) * 13201 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003118562767 + 0.003164434523 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13201

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13201
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13201 BstLean.Part154.csC) (piBar (rhoBar 13201 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13201 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13201 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13201 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13201 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13201 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13201 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13201 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13201 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13201 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13201 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051468051198 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13201) ≤ 0.010394110230 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13201 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035117219844)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010394110230 + 2 * 0.737676 / 13201) := by gcongr
    _ ≤ (0.051468051198 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13201 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13201

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13201
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525365139 : ℝ) ≤ plow 13201 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13201) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286490892)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326214915) : eMP 13201 0.011 xi bn ≤ 0.001142404451 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13201 : ℝ) * (1 - 0.011))) ≤ 0.000564911419 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326214915 / (13201 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564911419 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564911419 : ℝ) + 3.141593 * 0.052286490892 / (13201 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142404451 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286490892)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326214915) : PiBarMP 13201 12 0.011 xi bn ≤ 0.158131569472 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13201 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036417233764 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.261931543274 : ℝ) ≤ √((13201 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.895604789739 : ℝ) ≤ √(13201 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13201) ≤ 0.121261455460 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036417233764 + 0.052286490892 * 1.772454 / (2 * (114.261931543274 : ℝ))) * (1 + 0.001142404451) +
        8 / (13201 * 114.895604789739) + 0.121261455460 := by gcongr
    _ ≤ (0.158131569472 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286490892)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326214915) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280130446209) :
    parallelOracle 13201 0.011 xi bn cd ≤ 0.159084728715 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13201 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13201 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525365139 : ℝ) ≤ plow 13201 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.895604789739 : ℝ) ≤ √(13201 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280130446209 : ℝ) / (2 * 0.560525365139 * 114.895604789739)) * 0.158131569472 +
        0.280130446209 ^ 2 / (2 * 0.560525365139 * 114.895604789739) := by gcongr
    _ ≤ (0.159084728715 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286490892) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326214915)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280130446209) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13201 13201 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525365139 : ℝ) ≤ plow 13201 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.895604789739 : ℝ) ≤ √(13201 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13201 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13201 Θ 1.22 ≤ 0.011541786150 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.895604789739 := by gcongr <;> linarith
      _ ≤ (0.011541786150 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13201 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13201 13201 0.011 ≤ 0.008319612325 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13201 13201 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13201 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13201 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13201 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13201 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159084728715 + 0.011541786150 + (0.008319612325 : ℝ) *
        (1 + 2 * (0.280130446209 + 0.011541786150) / (0.560525365139 * 114.895604789739))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13201]

end BstLean.Part269.N13201

/-! The original eight local profiles supply actual 13201 moment certificates. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13201 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052286490892 ∧
    0 ≤ bN 13201 BstLean.Part154.csC (groupTheta g) ∧ bN 13201 BstLean.Part154.csC (groupTheta g) ≤ 0.001326214915 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13201 13201 0.011
      (momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13201 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13201 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13201 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228662395011 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13201 0.011
      (momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13201 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13201
/-! The actual computed-centre upper energy formula at 13201. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13201

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13201)
open BstLean.Part268 (cell13201)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084149137588
  | 2 => 0.085071393709
  | 3 => 0.085988929478
  | 4 => 0.086902488497
  | 5 => 0.087812988936
  | 6 => 0.088721551721
  | 7 => 0.089629531797
  | 8 => 0.090538552619
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13201 13201 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13201 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13201

/-! Actual upper energy certificates on all 43 source endpoints at 13201. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13201)
open BstLean.Part268 (cell13201)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13201 (gMinus 13201) (1 - (cell13201 i).lower) ≤ 1 ∧
    energyUpper 13201 (gMinus 13201) (BstLean.Part211.gPlus 13201)
      (finiteEnergy 13201 13201 0.011) (1 - (cell13201 i).lower) ≤
      (cell13201 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨10,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨11,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨12,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨13,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨14,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨15,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨16,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨17,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨18,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨19,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨20,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨21,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨22,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨23,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨24,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨25,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨26,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨27,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨28,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨29,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨30,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨31,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨32,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨33,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨34,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨35,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨36,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨37,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨38,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨39,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨40,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨41,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨42,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨43,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨44,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨45,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨46,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨47,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨48,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨49,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨50,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨51,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13201) (by norm_num)
        (q := 1 - (cell13201 ⟨52,by decide⟩).lower)
        (by norm_num [cell13201]) (by norm_num [cell13201])
      exact ⟨E.1,E.2.trans (by norm_num [cell13201])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13201

/-! Source-cell containment and simple scalar guards at 13201. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13201)
open BstLean.Part268 (cell13201)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13201 ⟨10,by decide⟩).lower ∧ (cell13201 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13201 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13201 ⟨11,by decide⟩).lower ∧ (cell13201 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13201 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13201 ⟨12,by decide⟩).lower ∧ (cell13201 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13201 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13201 ⟨13,by decide⟩).lower ∧ (cell13201 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13201 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13201 ⟨14,by decide⟩).lower ∧ (cell13201 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13201 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13201 ⟨15,by decide⟩).lower ∧ (cell13201 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13201 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13201 ⟨16,by decide⟩).lower ∧ (cell13201 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13201 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13201 ⟨17,by decide⟩).lower ∧ (cell13201 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13201 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13201 ⟨18,by decide⟩).lower ∧ (cell13201 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13201 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13201 ⟨19,by decide⟩).lower ∧ (cell13201 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13201 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13201 ⟨20,by decide⟩).lower ∧ (cell13201 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13201 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13201 ⟨21,by decide⟩).lower ∧ (cell13201 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13201 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13201 ⟨22,by decide⟩).lower ∧ (cell13201 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13201 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13201 ⟨23,by decide⟩).lower ∧ (cell13201 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13201 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13201 ⟨24,by decide⟩).lower ∧ (cell13201 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13201 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13201 ⟨25,by decide⟩).lower ∧ (cell13201 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13201 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13201 ⟨26,by decide⟩).lower ∧ (cell13201 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13201 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13201 ⟨27,by decide⟩).lower ∧ (cell13201 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13201 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13201 ⟨28,by decide⟩).lower ∧ (cell13201 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13201 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13201 ⟨29,by decide⟩).lower ∧ (cell13201 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13201 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13201 ⟨30,by decide⟩).lower ∧ (cell13201 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13201 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13201 ⟨31,by decide⟩).lower ∧ (cell13201 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13201 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13201 ⟨32,by decide⟩).lower ∧ (cell13201 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13201 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13201 ⟨33,by decide⟩).lower ∧ (cell13201 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13201 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13201 ⟨34,by decide⟩).lower ∧ (cell13201 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13201 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13201 ⟨35,by decide⟩).lower ∧ (cell13201 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13201 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13201 ⟨36,by decide⟩).lower ∧ (cell13201 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13201 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13201 ⟨37,by decide⟩).lower ∧ (cell13201 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13201 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13201 ⟨38,by decide⟩).lower ∧ (cell13201 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13201 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13201 ⟨39,by decide⟩).lower ∧ (cell13201 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13201 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13201 ⟨40,by decide⟩).lower ∧ (cell13201 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13201 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13201 ⟨41,by decide⟩).lower ∧ (cell13201 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13201 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13201 ⟨42,by decide⟩).lower ∧ (cell13201 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13201 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13201 ⟨43,by decide⟩).lower ∧ (cell13201 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13201 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13201 ⟨44,by decide⟩).lower ∧ (cell13201 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13201 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13201 ⟨45,by decide⟩).lower ∧ (cell13201 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13201 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13201 ⟨46,by decide⟩).lower ∧ (cell13201 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13201 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13201 ⟨47,by decide⟩).lower ∧ (cell13201 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13201 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13201 ⟨48,by decide⟩).lower ∧ (cell13201 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13201 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13201 ⟨49,by decide⟩).lower ∧ (cell13201 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13201 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13201 ⟨50,by decide⟩).lower ∧ (cell13201 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13201 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13201 ⟨51,by decide⟩).lower ∧ (cell13201 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13201 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13201 ⟨52,by decide⟩).lower ∧ (cell13201 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13201 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13201 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13201 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13201,cell13201,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13201 i).lower ∧
    (cell13201 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13201 i).upper ≤ (0.532 : ℝ) ∧
    (cell13201 i).centre ≤ (0.1 : ℝ) ∧ (cell13201 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13201 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13201 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13201

/-! The local source numeric instances at 13201 have no network premises. -/
namespace BstLean.Part269.N13201
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13201)
open BstLean.Part268 (cell13201)

noncomputable def sourceNumerics13201 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13201 (cell13201 i)
      scalarRow13201.M scalarRow13201.H scalarRow13201.xi := by
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
    energy_allowance := scalarRow13201.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13201]
    centre_nonneg := (scalarRow13201.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13201])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13201
/-! Actual 13202 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13202 ≤ (1.035115878347 : ℝ) := by
  have hr : (114.899956483890 : ℝ) ≤ √(13202 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.899956483890 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13202 13202 (11 / 1000) ≤
    (0.008319297227 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13202) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.899956483890 : ℝ) ≤ √(13202 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13202)
  have hdiv : K / √(13202 : ℝ) ≤ K / 114.899956483890 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.899956483890 ≤ (0.008319297227 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13202.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13202 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13202 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13202 := gPlus_lower 13202
end BstLean.Part269.N13202

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13202
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035115878346 : ℝ) ≤ wn 13202 := by
  have hn : √(13202 : ℝ) ≤ 114.899956483891 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13202 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.899956483891 ≤ 2 / √(13202 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242141023 : ℝ) ≤ rhoBar 13202 BstLean.Part154.csC ∧
    rhoBar 13202 BstLean.Part154.csC ≤ 0.000242141398 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035115878346 : ℝ) / (1.295212 * 13202) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035115878347 : ℝ) / (1.29521 * 13202) := by gcongr
      _ ≤ (0.000242141398 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13202 BstLean.Part154.csC) ≤ 0.000968624225 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13202 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) ≤ 0.000184948901 ∧
    cc1 (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) ≤ 0.000117684282 ∧
    cc2 (rhoBar 13202 BstLean.Part154.csC) ≤ 0.000068316711 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13202 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13202 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13202 BstLean.Part154.csC * nuR (rhoBar 13202 BstLean.Part154.csC)) ≤ 0.000484297455 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242141398 : ℝ) * 0.000968624225 := by gcongr
      _ ≤ (0.000484297455 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13202 BstLean.Part154.csC) * nuR (rhoBar 13202 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968624225 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13202 BstLean.Part154.csC) * rhoBar 13202 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242141398 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242141398 / 2 + 0.399 * 0.000968624225 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184948901 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484297455 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117684282 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242141398 / 1.414213562 := by gcongr
      _ ≤ (0.000068316711 : ℝ) := by norm_num

end BstLean.Part269.N13202

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13202
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) ≤ 1.47720E-7 := by
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13202 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13202 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13202 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184948901 : ℝ) ^ 2 + 0.000117684282 ^ 2 + 3 * 0.000068316711 ^ 2 +
        2 * 0.797885 * 0.000184948901 * 0.000117684282 + 2 * 0.000184948901 * 0.000068316711 +
        4 * 0.797885 * 0.000117684282 * 0.000068316711 := by gcongr
    _ ≤ (1.47720E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13202 BstLean.Part154.csC Θ ≤ 0.002525921724 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13202 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13202 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13202 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035115878347 * 1.47720E-7 / (0.000242141023 : ℝ) := by gcongr
    _ ≤ 0.002525921724 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13202 BstLean.Part154.csC Θ ≤ 0.002800768923 + 0.000638260872 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13202 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13202 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035115878347 : ℝ) * ((2 * Θ * 0.000242141398 +
        (6863 / 10000) * 0.000242141398 * 13202 * 0.000968624225) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002800768923 + 0.000638260872 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13202 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13202 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13202 0.011 Θ ∧ gammaRatio 13202 0.011 Θ ≤ 0.000083241951 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13202 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035115878347 : ℝ) * 0.525 / ((1 - 0.011) * 13202) := by gcongr
      _ ≤ (0.000083241951 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13202 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13202 0.011 Θ) :=
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
    badAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13202 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13202 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13202 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13202 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13202 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13202 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13202 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13202 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13202 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13202 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035115878347 : ℝ) * 13202 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003118339689 + 0.003164182596 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13202

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13202
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13202 BstLean.Part154.csC) (piBar (rhoBar 13202 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13202 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13202 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13202 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13202 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13202 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13202 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13202 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13202 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13202 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13202 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051466081174 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13202) ≤ 0.010393716566 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13202 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035115878347)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010393716566 + 2 * 0.737676 / 13202) := by gcongr
    _ ≤ (0.051466081174 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13202 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13202

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13202
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525406991 : ℝ) ≤ plow 13202 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13202) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286135552)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326108906) : eMP 13202 0.011 xi bn ≤ 0.001142315466 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13202 : ℝ) * (1 - 0.011))) ≤ 0.000564867446 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326108906 / (13202 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564867446 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564867446 : ℝ) + 3.141593 * 0.052286135552 / (13202 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142315466 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286135552)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326108906) : PiBarMP 13202 12 0.011 xi bn ≤ 0.158125497663 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13202 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036415778257 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.266259236924 : ℝ) ≤ √((13202 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.899956483890 : ℝ) ≤ √(13202 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13202) ≤ 0.121256862832 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036415778257 + 0.052286135552 * 1.772454 / (2 * (114.266259236924 : ℝ))) * (1 + 0.001142315466) +
        8 / (13202 * 114.899956483890) + 0.121256862832 := by gcongr
    _ ≤ (0.158125497663 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286135552)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326108906) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280127699187) :
    parallelOracle 13202 0.011 xi bn cd ≤ 0.159078592210 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13202 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13202 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525406991 : ℝ) ≤ plow 13202 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.899956483890 : ℝ) ≤ √(13202 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280127699187 : ℝ) / (2 * 0.560525406991 * 114.899956483890)) * 0.158125497663 +
        0.280127699187 ^ 2 / (2 * 0.560525406991 * 114.899956483890) := by gcongr
    _ ≤ (0.159078592210 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052286135552) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326108906)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280127699187) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13202 13202 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525406991 : ℝ) ≤ plow 13202 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.899956483890 : ℝ) ≤ √(13202 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13202 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13202 Θ 1.22 ≤ 0.011541349019 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.899956483890 := by gcongr <;> linarith
      _ ≤ (0.011541349019 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13202 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13202 13202 0.011 ≤ 0.008319297227 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13202 13202 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13202 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13202 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13202 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13202 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159078592210 + 0.011541349019 + (0.008319297227 : ℝ) *
        (1 + 2 * (0.280127699187 + 0.011541349019) / (0.560525406991 * 114.899956483890))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13202]

end BstLean.Part269.N13202

/-! The original eight local profiles supply actual 13202 moment certificates. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13202 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052286135552 ∧
    0 ≤ bN 13202 BstLean.Part154.csC (groupTheta g) ∧ bN 13202 BstLean.Part154.csC (groupTheta g) ≤ 0.001326108906 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13202 13202 0.011
      (momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13202 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13202 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13202 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228661618013 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13202 0.011
      (momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13202 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13202
/-! The actual computed-centre upper energy formula at 13202. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13202

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13202)
open BstLean.Part268 (cell13202)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084146667757
  | 2 => 0.085068894380
  | 3 => 0.085986396615
  | 4 => 0.086899917087
  | 5 => 0.087810372812
  | 6 => 0.088718883347
  | 7 => 0.089626802038
  | 8 => 0.090535750472
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13202 13202 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13202 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13202

/-! Actual upper energy certificates on all 43 source endpoints at 13202. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13202)
open BstLean.Part268 (cell13202)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13202 (gMinus 13202) (1 - (cell13202 i).lower) ≤ 1 ∧
    energyUpper 13202 (gMinus 13202) (BstLean.Part211.gPlus 13202)
      (finiteEnergy 13202 13202 0.011) (1 - (cell13202 i).lower) ≤
      (cell13202 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨10,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨11,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨12,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨13,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨14,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨15,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨16,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨17,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨18,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨19,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨20,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨21,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨22,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨23,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨24,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨25,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨26,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨27,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨28,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨29,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨30,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨31,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨32,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨33,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨34,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨35,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨36,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨37,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨38,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨39,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨40,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨41,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨42,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨43,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨44,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨45,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨46,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨47,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨48,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨49,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨50,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨51,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13202) (by norm_num)
        (q := 1 - (cell13202 ⟨52,by decide⟩).lower)
        (by norm_num [cell13202]) (by norm_num [cell13202])
      exact ⟨E.1,E.2.trans (by norm_num [cell13202])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13202

/-! Source-cell containment and simple scalar guards at 13202. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13202)
open BstLean.Part268 (cell13202)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13202 ⟨10,by decide⟩).lower ∧ (cell13202 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13202 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13202 ⟨11,by decide⟩).lower ∧ (cell13202 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13202 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13202 ⟨12,by decide⟩).lower ∧ (cell13202 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13202 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13202 ⟨13,by decide⟩).lower ∧ (cell13202 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13202 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13202 ⟨14,by decide⟩).lower ∧ (cell13202 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13202 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13202 ⟨15,by decide⟩).lower ∧ (cell13202 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13202 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13202 ⟨16,by decide⟩).lower ∧ (cell13202 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13202 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13202 ⟨17,by decide⟩).lower ∧ (cell13202 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13202 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13202 ⟨18,by decide⟩).lower ∧ (cell13202 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13202 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13202 ⟨19,by decide⟩).lower ∧ (cell13202 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13202 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13202 ⟨20,by decide⟩).lower ∧ (cell13202 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13202 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13202 ⟨21,by decide⟩).lower ∧ (cell13202 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13202 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13202 ⟨22,by decide⟩).lower ∧ (cell13202 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13202 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13202 ⟨23,by decide⟩).lower ∧ (cell13202 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13202 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13202 ⟨24,by decide⟩).lower ∧ (cell13202 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13202 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13202 ⟨25,by decide⟩).lower ∧ (cell13202 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13202 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13202 ⟨26,by decide⟩).lower ∧ (cell13202 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13202 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13202 ⟨27,by decide⟩).lower ∧ (cell13202 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13202 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13202 ⟨28,by decide⟩).lower ∧ (cell13202 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13202 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13202 ⟨29,by decide⟩).lower ∧ (cell13202 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13202 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13202 ⟨30,by decide⟩).lower ∧ (cell13202 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13202 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13202 ⟨31,by decide⟩).lower ∧ (cell13202 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13202 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13202 ⟨32,by decide⟩).lower ∧ (cell13202 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13202 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13202 ⟨33,by decide⟩).lower ∧ (cell13202 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13202 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13202 ⟨34,by decide⟩).lower ∧ (cell13202 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13202 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13202 ⟨35,by decide⟩).lower ∧ (cell13202 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13202 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13202 ⟨36,by decide⟩).lower ∧ (cell13202 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13202 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13202 ⟨37,by decide⟩).lower ∧ (cell13202 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13202 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13202 ⟨38,by decide⟩).lower ∧ (cell13202 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13202 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13202 ⟨39,by decide⟩).lower ∧ (cell13202 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13202 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13202 ⟨40,by decide⟩).lower ∧ (cell13202 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13202 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13202 ⟨41,by decide⟩).lower ∧ (cell13202 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13202 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13202 ⟨42,by decide⟩).lower ∧ (cell13202 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13202 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13202 ⟨43,by decide⟩).lower ∧ (cell13202 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13202 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13202 ⟨44,by decide⟩).lower ∧ (cell13202 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13202 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13202 ⟨45,by decide⟩).lower ∧ (cell13202 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13202 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13202 ⟨46,by decide⟩).lower ∧ (cell13202 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13202 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13202 ⟨47,by decide⟩).lower ∧ (cell13202 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13202 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13202 ⟨48,by decide⟩).lower ∧ (cell13202 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13202 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13202 ⟨49,by decide⟩).lower ∧ (cell13202 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13202 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13202 ⟨50,by decide⟩).lower ∧ (cell13202 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13202 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13202 ⟨51,by decide⟩).lower ∧ (cell13202 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13202 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13202 ⟨52,by decide⟩).lower ∧ (cell13202 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13202 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13202 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13202 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13202,cell13202,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13202 i).lower ∧
    (cell13202 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13202 i).upper ≤ (0.532 : ℝ) ∧
    (cell13202 i).centre ≤ (0.1 : ℝ) ∧ (cell13202 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13202 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13202 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13202

/-! The local source numeric instances at 13202 have no network premises. -/
namespace BstLean.Part269.N13202
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13202)
open BstLean.Part268 (cell13202)

noncomputable def sourceNumerics13202 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13202 (cell13202 i)
      scalarRow13202.M scalarRow13202.H scalarRow13202.xi := by
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
    energy_allowance := scalarRow13202.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13202]
    centre_nonneg := (scalarRow13202.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13202])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13202
/-! Actual 13203 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13203 ≤ (1.035114537004 : ℝ) := by
  have hr : (114.904308013233 : ℝ) ≤ √(13203 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.904308013233 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13203 13203 (11 / 1000) ≤
    (0.008318982166 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13203) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.904308013233 : ℝ) ≤ √(13203 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13203)
  have hdiv : K / √(13203 : ℝ) ≤ K / 114.904308013233 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.904308013233 ≤ (0.008318982166 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13203.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13203 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13203 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13203 := gPlus_lower 13203
end BstLean.Part269.N13203

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13203
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035114537003 : ℝ) ≤ wn 13203 := by
  have hn : √(13203 : ℝ) ≤ 114.904308013234 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13203 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.904308013234 ≤ 2 / √(13203 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242122370 : ℝ) ≤ rhoBar 13203 BstLean.Part154.csC ∧
    rhoBar 13203 BstLean.Part154.csC ≤ 0.000242122744 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035114537003 : ℝ) / (1.295212 * 13203) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035114537004 : ℝ) / (1.29521 * 13203) := by gcongr
      _ ≤ (0.000242122744 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13203 BstLean.Part154.csC) ≤ 0.000968549600 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13203 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) ≤ 0.000184934652 ∧
    cc1 (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) ≤ 0.000117675215 ∧
    cc2 (rhoBar 13203 BstLean.Part154.csC) ≤ 0.000068311448 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13203 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13203 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13203 BstLean.Part154.csC * nuR (rhoBar 13203 BstLean.Part154.csC)) ≤ 0.000484260144 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242122744 : ℝ) * 0.000968549600 := by gcongr
      _ ≤ (0.000484260144 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13203 BstLean.Part154.csC) * nuR (rhoBar 13203 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968549600 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13203 BstLean.Part154.csC) * rhoBar 13203 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242122744 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242122744 / 2 + 0.399 * 0.000968549600 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184934652 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484260144 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117675215 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242122744 / 1.414213562 := by gcongr
      _ ≤ (0.000068311448 : ℝ) := by norm_num

end BstLean.Part269.N13203

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13203
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) ≤ 1.47697E-7 := by
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13203 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13203 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13203 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184934652 : ℝ) ^ 2 + 0.000117675215 ^ 2 + 3 * 0.000068311448 ^ 2 +
        2 * 0.797885 * 0.000184934652 * 0.000117675215 + 2 * 0.000184934652 * 0.000068311448 +
        4 * 0.797885 * 0.000117675215 * 0.000068311448 := by gcongr
    _ ≤ (1.47697E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13203 BstLean.Part154.csC Θ ≤ 0.002525719731 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13203 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13203 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13203 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035114537004 * 1.47697E-7 / (0.000242122370 : ℝ) := by gcongr
    _ ≤ 0.002525719731 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13203 BstLean.Part154.csC Θ ≤ 0.002800545883 + 0.000638210875 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13203 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13203 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035114537004 : ℝ) * ((2 * Θ * 0.000242122744 +
        (6863 / 10000) * 0.000242122744 * 13203 * 0.000968549600) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002800545883 + 0.000638210875 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13203 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13203 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13203 0.011 Θ ∧ gammaRatio 13203 0.011 Θ ≤ 0.000083235539 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13203 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035114537004 : ℝ) * 0.525 / ((1 - 0.011) * 13203) := by gcongr
      _ ≤ (0.000083235539 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13203 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13203 0.011 Θ) :=
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
    badAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13203 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13203 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13203 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13203 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13203 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13203 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13203 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13203 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13203 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13203 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035114537004 : ℝ) * 13203 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003118116649 + 0.003163930606 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13203

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13203
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13203 BstLean.Part154.csC) (piBar (rhoBar 13203 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13203 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13203 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13203 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13203 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13203 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13203 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13203 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13203 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13203 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13203 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051464111372 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13203) ≤ 0.010393322946 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13203 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035114537004)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010393322946 + 2 * 0.737676 / 13203) := by gcongr
    _ ≤ (0.051464111372 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13203 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13203

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13203
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525448837 : ℝ) ≤ plow 13203 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13203) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285780218)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326002859) : eMP 13203 0.011 xi bn ≤ 0.001142226474 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13203 : ℝ) * (1 - 0.011))) ≤ 0.000564823469 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326002859 / (13203 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564823469 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564823469 : ℝ) + 3.141593 * 0.052285780218 / (13203 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142226474 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285780218)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326002859) : PiBarMP 13203 12 0.011 xi bn ≤ 0.158119425796 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13203 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036414322169 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.270586766674 : ℝ) ≤ √((13203 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.904308013233 : ℝ) ≤ √(13203 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13203) ≤ 0.121252270726 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036414322169 + 0.052285780218 * 1.772454 / (2 * (114.270586766674 : ℝ))) * (1 + 0.001142226474) +
        8 / (13203 * 114.904308013233) + 0.121252270726 := by gcongr
    _ ≤ (0.158119425796 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285780218)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326002859) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280124952397) :
    parallelOracle 13203 0.011 xi bn cd ≤ 0.159072455654 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13203 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13203 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525448837 : ℝ) ≤ plow 13203 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.904308013233 : ℝ) ≤ √(13203 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280124952397 : ℝ) / (2 * 0.560525448837 * 114.904308013233)) * 0.158119425796 +
        0.280124952397 ^ 2 / (2 * 0.560525448837 * 114.904308013233) := by gcongr
    _ ≤ (0.159072455654 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285780218) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326002859)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280124952397) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13203 13203 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525448837 : ℝ) ≤ plow 13203 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.904308013233 : ℝ) ≤ √(13203 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13203 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13203 Θ 1.22 ≤ 0.011540911938 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.904308013233 := by gcongr <;> linarith
      _ ≤ (0.011540911938 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13203 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13203 13203 0.011 ≤ 0.008318982166 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13203 13203 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13203 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13203 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13203 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13203 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159072455654 + 0.011540911938 + (0.008318982166 : ℝ) *
        (1 + 2 * (0.280124952397 + 0.011540911938) / (0.560525448837 * 114.904308013233))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13203]

end BstLean.Part269.N13203

/-! The original eight local profiles supply actual 13203 moment certificates. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13203 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052285780218 ∧
    0 ≤ bN 13203 BstLean.Part154.csC (groupTheta g) ∧ bN 13203 BstLean.Part154.csC (groupTheta g) ≤ 0.001326002859 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13203 13203 0.011
      (momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13203 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13203 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13203 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228660841025 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13203 0.011
      (momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13203 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13203
/-! The actual computed-centre upper energy formula at 13203. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13203

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13203)
open BstLean.Part268 (cell13203)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084144198600
  | 2 => 0.085066395747
  | 3 => 0.085983864475
  | 4 => 0.086897346436
  | 5 => 0.087807757488
  | 6 => 0.088716215824
  | 7 => 0.089624073191
  | 8 => 0.090532949313
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13203 13203 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13203 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13203

/-! Actual upper energy certificates on all 43 source endpoints at 13203. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13203)
open BstLean.Part268 (cell13203)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13203 (gMinus 13203) (1 - (cell13203 i).lower) ≤ 1 ∧
    energyUpper 13203 (gMinus 13203) (BstLean.Part211.gPlus 13203)
      (finiteEnergy 13203 13203 0.011) (1 - (cell13203 i).lower) ≤
      (cell13203 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨10,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨11,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨12,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨13,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨14,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨15,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨16,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨17,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨18,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨19,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨20,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨21,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨22,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨23,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨24,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨25,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨26,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨27,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨28,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨29,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨30,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨31,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨32,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨33,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨34,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨35,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨36,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨37,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨38,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨39,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨40,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨41,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨42,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨43,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨44,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨45,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨46,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨47,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨48,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨49,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨50,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨51,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13203) (by norm_num)
        (q := 1 - (cell13203 ⟨52,by decide⟩).lower)
        (by norm_num [cell13203]) (by norm_num [cell13203])
      exact ⟨E.1,E.2.trans (by norm_num [cell13203])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13203

/-! Source-cell containment and simple scalar guards at 13203. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13203)
open BstLean.Part268 (cell13203)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13203 ⟨10,by decide⟩).lower ∧ (cell13203 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13203 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13203 ⟨11,by decide⟩).lower ∧ (cell13203 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13203 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13203 ⟨12,by decide⟩).lower ∧ (cell13203 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13203 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13203 ⟨13,by decide⟩).lower ∧ (cell13203 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13203 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13203 ⟨14,by decide⟩).lower ∧ (cell13203 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13203 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13203 ⟨15,by decide⟩).lower ∧ (cell13203 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13203 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13203 ⟨16,by decide⟩).lower ∧ (cell13203 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13203 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13203 ⟨17,by decide⟩).lower ∧ (cell13203 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13203 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13203 ⟨18,by decide⟩).lower ∧ (cell13203 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13203 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13203 ⟨19,by decide⟩).lower ∧ (cell13203 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13203 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13203 ⟨20,by decide⟩).lower ∧ (cell13203 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13203 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13203 ⟨21,by decide⟩).lower ∧ (cell13203 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13203 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13203 ⟨22,by decide⟩).lower ∧ (cell13203 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13203 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13203 ⟨23,by decide⟩).lower ∧ (cell13203 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13203 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13203 ⟨24,by decide⟩).lower ∧ (cell13203 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13203 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13203 ⟨25,by decide⟩).lower ∧ (cell13203 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13203 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13203 ⟨26,by decide⟩).lower ∧ (cell13203 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13203 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13203 ⟨27,by decide⟩).lower ∧ (cell13203 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13203 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13203 ⟨28,by decide⟩).lower ∧ (cell13203 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13203 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13203 ⟨29,by decide⟩).lower ∧ (cell13203 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13203 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13203 ⟨30,by decide⟩).lower ∧ (cell13203 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13203 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13203 ⟨31,by decide⟩).lower ∧ (cell13203 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13203 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13203 ⟨32,by decide⟩).lower ∧ (cell13203 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13203 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13203 ⟨33,by decide⟩).lower ∧ (cell13203 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13203 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13203 ⟨34,by decide⟩).lower ∧ (cell13203 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13203 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13203 ⟨35,by decide⟩).lower ∧ (cell13203 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13203 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13203 ⟨36,by decide⟩).lower ∧ (cell13203 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13203 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13203 ⟨37,by decide⟩).lower ∧ (cell13203 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13203 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13203 ⟨38,by decide⟩).lower ∧ (cell13203 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13203 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13203 ⟨39,by decide⟩).lower ∧ (cell13203 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13203 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13203 ⟨40,by decide⟩).lower ∧ (cell13203 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13203 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13203 ⟨41,by decide⟩).lower ∧ (cell13203 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13203 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13203 ⟨42,by decide⟩).lower ∧ (cell13203 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13203 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13203 ⟨43,by decide⟩).lower ∧ (cell13203 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13203 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13203 ⟨44,by decide⟩).lower ∧ (cell13203 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13203 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13203 ⟨45,by decide⟩).lower ∧ (cell13203 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13203 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13203 ⟨46,by decide⟩).lower ∧ (cell13203 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13203 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13203 ⟨47,by decide⟩).lower ∧ (cell13203 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13203 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13203 ⟨48,by decide⟩).lower ∧ (cell13203 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13203 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13203 ⟨49,by decide⟩).lower ∧ (cell13203 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13203 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13203 ⟨50,by decide⟩).lower ∧ (cell13203 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13203 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13203 ⟨51,by decide⟩).lower ∧ (cell13203 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13203 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13203 ⟨52,by decide⟩).lower ∧ (cell13203 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13203 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13203 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13203 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13203,cell13203,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13203 i).lower ∧
    (cell13203 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13203 i).upper ≤ (0.532 : ℝ) ∧
    (cell13203 i).centre ≤ (0.1 : ℝ) ∧ (cell13203 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13203 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13203 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13203

/-! The local source numeric instances at 13203 have no network premises. -/
namespace BstLean.Part269.N13203
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13203)
open BstLean.Part268 (cell13203)

noncomputable def sourceNumerics13203 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13203 (cell13203 i)
      scalarRow13203.M scalarRow13203.H scalarRow13203.xi := by
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
    energy_allowance := scalarRow13203.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13203]
    centre_nonneg := (scalarRow13203.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13203])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13203
/-! Actual 13204 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13204 ≤ (1.035113195813 : ℝ) := by
  have hr : (114.908659377785 : ℝ) ≤ √(13204 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.908659377785 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13204 13204 (11 / 1000) ≤
    (0.008318667140 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13204) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.908659377785 : ℝ) ≤ √(13204 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13204)
  have hdiv : K / √(13204 : ℝ) ≤ K / 114.908659377785 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.908659377785 ≤ (0.008318667140 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13204.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13204 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13204 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13204 := gPlus_lower 13204
end BstLean.Part269.N13204

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13204
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035113195812 : ℝ) ≤ wn 13204 := by
  have hn : √(13204 : ℝ) ≤ 114.908659377786 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13204 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.908659377786 ≤ 2 / √(13204 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242103719 : ℝ) ≤ rhoBar 13204 BstLean.Part154.csC ∧
    rhoBar 13204 BstLean.Part154.csC ≤ 0.000242104094 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035113195812 : ℝ) / (1.295212 * 13204) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035113195813 : ℝ) / (1.29521 * 13204) := by gcongr
      _ ≤ (0.000242104094 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13204 BstLean.Part154.csC) ≤ 0.000968474991 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13204 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) ≤ 0.000184920406 ∧
    cc1 (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) ≤ 0.000117666151 ∧
    cc2 (rhoBar 13204 BstLean.Part154.csC) ≤ 0.000068306186 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13204 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13204 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13204 BstLean.Part154.csC * nuR (rhoBar 13204 BstLean.Part154.csC)) ≤ 0.000484222842 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242104094 : ℝ) * 0.000968474991 := by gcongr
      _ ≤ (0.000484222842 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13204 BstLean.Part154.csC) * nuR (rhoBar 13204 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968474991 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13204 BstLean.Part154.csC) * rhoBar 13204 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242104094 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242104094 / 2 + 0.399 * 0.000968474991 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184920406 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484222842 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117666151 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242104094 / 1.414213562 := by gcongr
      _ ≤ (0.000068306186 : ℝ) := by norm_num

end BstLean.Part269.N13204

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13204
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) ≤ 1.47675E-7 := by
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13204 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13204 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13204 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184920406 : ℝ) ^ 2 + 0.000117666151 ^ 2 + 3 * 0.000068306186 ^ 2 +
        2 * 0.797885 * 0.000184920406 * 0.000117666151 + 2 * 0.000184920406 * 0.000068306186 +
        4 * 0.797885 * 0.000117666151 * 0.000068306186 := by gcongr
    _ ≤ (1.47675E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13204 BstLean.Part154.csC Θ ≤ 0.002525534789 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13204 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13204 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13204 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035113195813 * 1.47675E-7 / (0.000242103719 : ℝ) := by gcongr
    _ ≤ 0.002525534789 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13204 BstLean.Part154.csC Θ ≤ 0.002800322904 + 0.000638160888 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13204 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13204 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035113195813 : ℝ) * ((2 * Θ * 0.000242104094 +
        (6863 / 10000) * 0.000242104094 * 13204 * 0.000968474991) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002800322904 + 0.000638160888 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13204 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13204 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13204 0.011 Θ ∧ gammaRatio 13204 0.011 Θ ≤ 0.000083229127 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13204 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035113195813 : ℝ) * 0.525 / ((1 - 0.011) * 13204) := by gcongr
      _ ≤ (0.000083229127 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13204 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13204 0.011 Θ) :=
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
    badAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13204 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13204 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13204 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13204 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13204 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13204 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13204 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13204 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13204 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13204 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035113195813 : ℝ) * 13204 *
        (1.1283E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003117893670 + 0.003163695677 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13204

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13204
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13204 BstLean.Part154.csC) (piBar (rhoBar 13204 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13204 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13204 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13204 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13204 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13204 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13204 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13204 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13204 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13204 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13204 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051462141801 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13204) ≤ 0.010392929372 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13204 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035113195813)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010392929372 + 2 * 0.737676 / 13204) := by gcongr
    _ ≤ (0.051462141801 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13204 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13204

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13204
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525490677 : ℝ) ≤ plow 13204 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13204) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285433901)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325905765) : eMP 13204 0.011 xi bn ≤ 0.001142141302 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13204 : ℝ) * (1 - 0.011))) ≤ 0.000564781401 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325905765 / (13204 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564781401 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564781401 : ℝ) + 3.141593 * 0.052285433901 / (13204 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142141302 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285433901)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325905765) : PiBarMP 13204 12 0.011 xi bn ≤ 0.158113477682 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13204 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036412988960 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.274914132542 : ℝ) ≤ √((13204 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.908659377785 : ℝ) ≤ √(13204 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13204) ≤ 0.121247679141 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036412988960 + 0.052285433901 * 1.772454 / (2 * (114.274914132542 : ℝ))) * (1 + 0.001142141302) +
        8 / (13204 * 114.908659377785) + 0.121247679141 := by gcongr
    _ ≤ (0.158113477682 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285433901)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325905765) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280122225552) :
    parallelOracle 13204 0.011 xi bn cd ≤ 0.159066443239 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13204 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13204 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525490677 : ℝ) ≤ plow 13204 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.908659377785 : ℝ) ≤ √(13204 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280122225552 : ℝ) / (2 * 0.560525490677 * 114.908659377785)) * 0.158113477682 +
        0.280122225552 ^ 2 / (2 * 0.560525490677 * 114.908659377785) := by gcongr
    _ ≤ (0.159066443239 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285433901) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325905765)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280122225552) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13204 13204 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525490677 : ℝ) ≤ plow 13204 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.908659377785 : ℝ) ≤ √(13204 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13204 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13204 Θ 1.22 ≤ 0.011540474906 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.908659377785 := by gcongr <;> linarith
      _ ≤ (0.011540474906 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13204 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13204 13204 0.011 ≤ 0.008318667140 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13204 13204 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13204 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13204 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13204 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13204 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159066443239 + 0.011540474906 + (0.008318667140 : ℝ) *
        (1 + 2 * (0.280122225552 + 0.011540474906) / (0.560525490677 * 114.908659377785))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13204]

end BstLean.Part269.N13204

/-! The original eight local profiles supply actual 13204 moment certificates. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13204 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052285433901 ∧
    0 ≤ bN 13204 BstLean.Part154.csC (groupTheta g) ∧ bN 13204 BstLean.Part154.csC (groupTheta g) ≤ 0.001325905765 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13204 13204 0.011
      (momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13204 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13204 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13204 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228660083751 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13204 0.011
      (momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13204 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13204
/-! The actual computed-centre upper energy formula at 13204. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13204

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13204)
open BstLean.Part268 (cell13204)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084141730116
  | 2 => 0.085063897811
  | 3 => 0.085981333059
  | 4 => 0.086894776541
  | 5 => 0.087805142962
  | 6 => 0.088713549150
  | 7 => 0.089621345255
  | 8 => 0.090530149140
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13204 13204 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13204 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13204

/-! Actual upper energy certificates on all 43 source endpoints at 13204. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13204)
open BstLean.Part268 (cell13204)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13204 (gMinus 13204) (1 - (cell13204 i).lower) ≤ 1 ∧
    energyUpper 13204 (gMinus 13204) (BstLean.Part211.gPlus 13204)
      (finiteEnergy 13204 13204 0.011) (1 - (cell13204 i).lower) ≤
      (cell13204 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨10,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨11,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨12,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨13,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨14,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨15,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨16,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨17,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨18,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨19,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨20,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨21,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨22,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨23,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨24,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨25,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨26,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨27,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨28,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨29,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨30,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨31,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨32,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨33,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨34,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨35,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨36,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨37,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨38,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨39,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨40,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨41,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨42,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨43,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨44,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨45,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨46,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨47,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨48,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨49,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨50,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨51,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13204) (by norm_num)
        (q := 1 - (cell13204 ⟨52,by decide⟩).lower)
        (by norm_num [cell13204]) (by norm_num [cell13204])
      exact ⟨E.1,E.2.trans (by norm_num [cell13204])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13204

/-! Source-cell containment and simple scalar guards at 13204. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13204)
open BstLean.Part268 (cell13204)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13204 ⟨10,by decide⟩).lower ∧ (cell13204 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13204 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13204 ⟨11,by decide⟩).lower ∧ (cell13204 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13204 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13204 ⟨12,by decide⟩).lower ∧ (cell13204 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13204 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13204 ⟨13,by decide⟩).lower ∧ (cell13204 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13204 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13204 ⟨14,by decide⟩).lower ∧ (cell13204 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13204 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13204 ⟨15,by decide⟩).lower ∧ (cell13204 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13204 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13204 ⟨16,by decide⟩).lower ∧ (cell13204 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13204 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13204 ⟨17,by decide⟩).lower ∧ (cell13204 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13204 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13204 ⟨18,by decide⟩).lower ∧ (cell13204 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13204 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13204 ⟨19,by decide⟩).lower ∧ (cell13204 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13204 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13204 ⟨20,by decide⟩).lower ∧ (cell13204 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13204 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13204 ⟨21,by decide⟩).lower ∧ (cell13204 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13204 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13204 ⟨22,by decide⟩).lower ∧ (cell13204 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13204 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13204 ⟨23,by decide⟩).lower ∧ (cell13204 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13204 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13204 ⟨24,by decide⟩).lower ∧ (cell13204 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13204 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13204 ⟨25,by decide⟩).lower ∧ (cell13204 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13204 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13204 ⟨26,by decide⟩).lower ∧ (cell13204 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13204 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13204 ⟨27,by decide⟩).lower ∧ (cell13204 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13204 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13204 ⟨28,by decide⟩).lower ∧ (cell13204 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13204 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13204 ⟨29,by decide⟩).lower ∧ (cell13204 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13204 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13204 ⟨30,by decide⟩).lower ∧ (cell13204 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13204 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13204 ⟨31,by decide⟩).lower ∧ (cell13204 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13204 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13204 ⟨32,by decide⟩).lower ∧ (cell13204 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13204 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13204 ⟨33,by decide⟩).lower ∧ (cell13204 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13204 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13204 ⟨34,by decide⟩).lower ∧ (cell13204 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13204 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13204 ⟨35,by decide⟩).lower ∧ (cell13204 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13204 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13204 ⟨36,by decide⟩).lower ∧ (cell13204 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13204 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13204 ⟨37,by decide⟩).lower ∧ (cell13204 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13204 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13204 ⟨38,by decide⟩).lower ∧ (cell13204 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13204 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13204 ⟨39,by decide⟩).lower ∧ (cell13204 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13204 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13204 ⟨40,by decide⟩).lower ∧ (cell13204 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13204 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13204 ⟨41,by decide⟩).lower ∧ (cell13204 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13204 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13204 ⟨42,by decide⟩).lower ∧ (cell13204 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13204 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13204 ⟨43,by decide⟩).lower ∧ (cell13204 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13204 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13204 ⟨44,by decide⟩).lower ∧ (cell13204 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13204 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13204 ⟨45,by decide⟩).lower ∧ (cell13204 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13204 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13204 ⟨46,by decide⟩).lower ∧ (cell13204 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13204 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13204 ⟨47,by decide⟩).lower ∧ (cell13204 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13204 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13204 ⟨48,by decide⟩).lower ∧ (cell13204 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13204 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13204 ⟨49,by decide⟩).lower ∧ (cell13204 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13204 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13204 ⟨50,by decide⟩).lower ∧ (cell13204 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13204 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13204 ⟨51,by decide⟩).lower ∧ (cell13204 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13204 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13204 ⟨52,by decide⟩).lower ∧ (cell13204 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13204 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13204 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13204 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13204,cell13204,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13204 i).lower ∧
    (cell13204 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13204 i).upper ≤ (0.532 : ℝ) ∧
    (cell13204 i).centre ≤ (0.1 : ℝ) ∧ (cell13204 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13204 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13204 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13204

/-! The local source numeric instances at 13204 have no network premises. -/
namespace BstLean.Part269.N13204
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13204)
open BstLean.Part268 (cell13204)

noncomputable def sourceNumerics13204 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13204 (cell13204 i)
      scalarRow13204.M scalarRow13204.H scalarRow13204.xi := by
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
    energy_allowance := scalarRow13204.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13204]
    centre_nonneg := (scalarRow13204.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13204])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13204
/-! Actual 13205 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13205 ≤ (1.035111854776 : ℝ) := by
  have hr : (114.913010577566 : ℝ) ≤ √(13205 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.913010577566 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13205 13205 (11 / 1000) ≤
    (0.008318352150 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13205) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.913010577566 : ℝ) ≤ √(13205 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13205)
  have hdiv : K / √(13205 : ℝ) ≤ K / 114.913010577566 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.913010577566 ≤ (0.008318352150 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13205.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13205 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13205 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13205 := gPlus_lower 13205
end BstLean.Part269.N13205

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13205
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035111854775 : ℝ) ≤ wn 13205 := by
  have hn : √(13205 : ℝ) ≤ 114.913010577567 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13205 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.913010577567 ≤ 2 / √(13205 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242085071 : ℝ) ≤ rhoBar 13205 BstLean.Part154.csC ∧
    rhoBar 13205 BstLean.Part154.csC ≤ 0.000242085446 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035111854775 : ℝ) / (1.295212 * 13205) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035111854776 : ℝ) / (1.29521 * 13205) := by gcongr
      _ ≤ (0.000242085446 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13205 BstLean.Part154.csC) ≤ 0.000968400390 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13205 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) ≤ 0.000184906162 ∧
    cc1 (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) ≤ 0.000117657088 ∧
    cc2 (rhoBar 13205 BstLean.Part154.csC) ≤ 0.000068300924 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13205 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13205 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13205 BstLean.Part154.csC * nuR (rhoBar 13205 BstLean.Part154.csC)) ≤ 0.000484185544 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242085446 : ℝ) * 0.000968400390 := by gcongr
      _ ≤ (0.000484185544 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13205 BstLean.Part154.csC) * nuR (rhoBar 13205 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968400390 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13205 BstLean.Part154.csC) * rhoBar 13205 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242085446 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242085446 / 2 + 0.399 * 0.000968400390 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184906162 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484185544 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117657088 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242085446 / 1.414213562 := by gcongr
      _ ≤ (0.000068300924 : ℝ) := by norm_num

end BstLean.Part269.N13205

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13205
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) ≤ 1.47652E-7 := by
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13205 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13205 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13205 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184906162 : ℝ) ^ 2 + 0.000117657088 ^ 2 + 3 * 0.000068300924 ^ 2 +
        2 * 0.797885 * 0.000184906162 * 0.000117657088 + 2 * 0.000184906162 * 0.000068300924 +
        4 * 0.797885 * 0.000117657088 * 0.000068300924 := by gcongr
    _ ≤ (1.47652E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13205 BstLean.Part154.csC Θ ≤ 0.002525332685 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13205 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13205 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13205 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035111854776 * 1.47652E-7 / (0.000242085071 : ℝ) := by gcongr
    _ ≤ 0.002525332685 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13205 BstLean.Part154.csC Θ ≤ 0.002800099941 + 0.000638110907 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13205 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13205 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035111854776 : ℝ) * ((2 * Θ * 0.000242085446 +
        (6863 / 10000) * 0.000242085446 * 13205 * 0.000968400390) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002800099941 + 0.000638110907 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13205 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13205 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13205 0.011 Θ ∧ gammaRatio 13205 0.011 Θ ≤ 0.000083222716 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13205 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035111854776 : ℝ) * 0.525 / ((1 - 0.011) * 13205) := by gcongr
      _ ≤ (0.000083222716 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13205 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13205 0.011 Θ) :=
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
    badAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13205 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13205 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13205 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13205 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13205 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13205 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13205 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13205 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13205 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13205 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035111854776 : ℝ) * 13205 *
        (1.1283E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003117670707 + 0.003163443592 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13205

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13205
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13205 BstLean.Part154.csC) (piBar (rhoBar 13205 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13205 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13205 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13205 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13205 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13205 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13205 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13205 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13205 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13205 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13205 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051460172452 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13205) ≤ 0.010392535842 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13205 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035111854776)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010392535842 + 2 * 0.737676 / 13205) := by gcongr
    _ ≤ (0.051460172452 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13205 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13205

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13205
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525532510 : ℝ) ≤ plow 13205 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13205) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285078593)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325799660) : eMP 13205 0.011 xi bn ≤ 0.001142052298 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13205 : ℝ) * (1 - 0.011))) ≤ 0.000564737418 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325799660 / (13205 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564737418 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564737418 : ℝ) + 3.141593 * 0.052285078593 / (13205 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142052298 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285078593)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325799660) : PiBarMP 13205 12 0.011 xi bn ≤ 0.158107405954 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13205 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036411531965 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.279241334548 : ℝ) ≤ √((13205 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.913010577566 : ℝ) ≤ √(13205 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13205) ≤ 0.121243088078 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036411531965 + 0.052285078593 * 1.772454 / (2 * (114.279241334548 : ℝ))) * (1 + 0.001142052298) +
        8 / (13205 * 114.913010577566) + 0.121243088078 := by gcongr
    _ ≤ (0.158107405954 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285078593)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325799660) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280119479267) :
    parallelOracle 13205 0.011 xi bn cd ≤ 0.159060306839 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13205 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13205 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525532510 : ℝ) ≤ plow 13205 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.913010577566 : ℝ) ≤ √(13205 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280119479267 : ℝ) / (2 * 0.560525532510 * 114.913010577566)) * 0.158107405954 +
        0.280119479267 ^ 2 / (2 * 0.560525532510 * 114.913010577566) := by gcongr
    _ ≤ (0.159060306839 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052285078593) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325799660)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280119479267) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13205 13205 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525532510 : ℝ) ≤ plow 13205 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.913010577566 : ℝ) ≤ √(13205 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13205 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13205 Θ 1.22 ≤ 0.011540037924 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.913010577566 := by gcongr <;> linarith
      _ ≤ (0.011540037924 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13205 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13205 13205 0.011 ≤ 0.008318352150 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13205 13205 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13205 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13205 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13205 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13205 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159060306839 + 0.011540037924 + (0.008318352150 : ℝ) *
        (1 + 2 * (0.280119479267 + 0.011540037924) / (0.560525532510 * 114.913010577566))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13205]

end BstLean.Part269.N13205

/-! The original eight local profiles supply actual 13205 moment certificates. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13205 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052285078593 ∧
    0 ≤ bN 13205 BstLean.Part154.csC (groupTheta g) ∧ bN 13205 BstLean.Part154.csC (groupTheta g) ≤ 0.001325799660 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13205 13205 0.011
      (momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13205 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13205 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13205 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228659306815 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13205 0.011
      (momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13205 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13205
/-! The actual computed-centre upper energy formula at 13205. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13205

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13205)
open BstLean.Part268 (cell13205)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084139262307
  | 2 => 0.085061400570
  | 3 => 0.085978802365
  | 4 => 0.086892207403
  | 5 => 0.087802529233
  | 6 => 0.088710883324
  | 7 => 0.089618618229
  | 8 => 0.090527349951
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13205 13205 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13205 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13205

/-! Actual upper energy certificates on all 43 source endpoints at 13205. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13205)
open BstLean.Part268 (cell13205)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13205 (gMinus 13205) (1 - (cell13205 i).lower) ≤ 1 ∧
    energyUpper 13205 (gMinus 13205) (BstLean.Part211.gPlus 13205)
      (finiteEnergy 13205 13205 0.011) (1 - (cell13205 i).lower) ≤
      (cell13205 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨10,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨11,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨12,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨13,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨14,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨15,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨16,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨17,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨18,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨19,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨20,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨21,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨22,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨23,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨24,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨25,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨26,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨27,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨28,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨29,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨30,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨31,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨32,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨33,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨34,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨35,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨36,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨37,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨38,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨39,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨40,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨41,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨42,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨43,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨44,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨45,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨46,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨47,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨48,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨49,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨50,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨51,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13205) (by norm_num)
        (q := 1 - (cell13205 ⟨52,by decide⟩).lower)
        (by norm_num [cell13205]) (by norm_num [cell13205])
      exact ⟨E.1,E.2.trans (by norm_num [cell13205])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13205

/-! Source-cell containment and simple scalar guards at 13205. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13205)
open BstLean.Part268 (cell13205)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13205 ⟨10,by decide⟩).lower ∧ (cell13205 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13205 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13205 ⟨11,by decide⟩).lower ∧ (cell13205 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13205 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13205 ⟨12,by decide⟩).lower ∧ (cell13205 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13205 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13205 ⟨13,by decide⟩).lower ∧ (cell13205 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13205 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13205 ⟨14,by decide⟩).lower ∧ (cell13205 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13205 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13205 ⟨15,by decide⟩).lower ∧ (cell13205 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13205 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13205 ⟨16,by decide⟩).lower ∧ (cell13205 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13205 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13205 ⟨17,by decide⟩).lower ∧ (cell13205 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13205 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13205 ⟨18,by decide⟩).lower ∧ (cell13205 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13205 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13205 ⟨19,by decide⟩).lower ∧ (cell13205 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13205 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13205 ⟨20,by decide⟩).lower ∧ (cell13205 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13205 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13205 ⟨21,by decide⟩).lower ∧ (cell13205 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13205 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13205 ⟨22,by decide⟩).lower ∧ (cell13205 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13205 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13205 ⟨23,by decide⟩).lower ∧ (cell13205 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13205 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13205 ⟨24,by decide⟩).lower ∧ (cell13205 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13205 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13205 ⟨25,by decide⟩).lower ∧ (cell13205 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13205 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13205 ⟨26,by decide⟩).lower ∧ (cell13205 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13205 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13205 ⟨27,by decide⟩).lower ∧ (cell13205 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13205 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13205 ⟨28,by decide⟩).lower ∧ (cell13205 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13205 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13205 ⟨29,by decide⟩).lower ∧ (cell13205 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13205 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13205 ⟨30,by decide⟩).lower ∧ (cell13205 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13205 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13205 ⟨31,by decide⟩).lower ∧ (cell13205 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13205 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13205 ⟨32,by decide⟩).lower ∧ (cell13205 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13205 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13205 ⟨33,by decide⟩).lower ∧ (cell13205 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13205 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13205 ⟨34,by decide⟩).lower ∧ (cell13205 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13205 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13205 ⟨35,by decide⟩).lower ∧ (cell13205 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13205 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13205 ⟨36,by decide⟩).lower ∧ (cell13205 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13205 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13205 ⟨37,by decide⟩).lower ∧ (cell13205 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13205 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13205 ⟨38,by decide⟩).lower ∧ (cell13205 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13205 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13205 ⟨39,by decide⟩).lower ∧ (cell13205 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13205 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13205 ⟨40,by decide⟩).lower ∧ (cell13205 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13205 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13205 ⟨41,by decide⟩).lower ∧ (cell13205 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13205 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13205 ⟨42,by decide⟩).lower ∧ (cell13205 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13205 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13205 ⟨43,by decide⟩).lower ∧ (cell13205 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13205 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13205 ⟨44,by decide⟩).lower ∧ (cell13205 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13205 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13205 ⟨45,by decide⟩).lower ∧ (cell13205 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13205 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13205 ⟨46,by decide⟩).lower ∧ (cell13205 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13205 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13205 ⟨47,by decide⟩).lower ∧ (cell13205 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13205 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13205 ⟨48,by decide⟩).lower ∧ (cell13205 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13205 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13205 ⟨49,by decide⟩).lower ∧ (cell13205 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13205 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13205 ⟨50,by decide⟩).lower ∧ (cell13205 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13205 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13205 ⟨51,by decide⟩).lower ∧ (cell13205 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13205 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13205 ⟨52,by decide⟩).lower ∧ (cell13205 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13205 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13205 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13205 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13205,cell13205,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13205 i).lower ∧
    (cell13205 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13205 i).upper ≤ (0.532 : ℝ) ∧
    (cell13205 i).centre ≤ (0.1 : ℝ) ∧ (cell13205 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13205 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13205 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13205

/-! The local source numeric instances at 13205 have no network premises. -/
namespace BstLean.Part269.N13205
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13205)
open BstLean.Part268 (cell13205)

noncomputable def sourceNumerics13205 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13205 (cell13205 i)
      scalarRow13205.M scalarRow13205.H scalarRow13205.xi := by
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
    energy_allowance := scalarRow13205.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13205]
    centre_nonneg := (scalarRow13205.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13205])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13205
/-! Actual 13206 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13206 ≤ (1.035110513892 : ℝ) := by
  have hr : (114.917361612595 : ℝ) ≤ √(13206 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.917361612595 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13206 13206 (11 / 1000) ≤
    (0.008318037196 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13206) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.917361612595 : ℝ) ≤ √(13206 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13206)
  have hdiv : K / √(13206 : ℝ) ≤ K / 114.917361612595 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.917361612595 ≤ (0.008318037196 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13206.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13206 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13206 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13206 := gPlus_lower 13206
end BstLean.Part269.N13206

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13206
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035110513891 : ℝ) ≤ wn 13206 := by
  have hn : √(13206 : ℝ) ≤ 114.917361612596 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13206 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.917361612596 ≤ 2 / √(13206 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242066426 : ℝ) ≤ rhoBar 13206 BstLean.Part154.csC ∧
    rhoBar 13206 BstLean.Part154.csC ≤ 0.000242066801 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035110513891 : ℝ) / (1.295212 * 13206) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035110513892 : ℝ) / (1.29521 * 13206) := by gcongr
      _ ≤ (0.000242066801 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13206 BstLean.Part154.csC) ≤ 0.000968325801 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13206 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) ≤ 0.000184891921 ∧
    cc1 (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) ≤ 0.000117648026 ∧
    cc2 (rhoBar 13206 BstLean.Part154.csC) ≤ 0.000068295664 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13206 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13206 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13206 BstLean.Part154.csC * nuR (rhoBar 13206 BstLean.Part154.csC)) ≤ 0.000484148252 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242066801 : ℝ) * 0.000968325801 := by gcongr
      _ ≤ (0.000484148252 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13206 BstLean.Part154.csC) * nuR (rhoBar 13206 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968325801 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13206 BstLean.Part154.csC) * rhoBar 13206 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242066801 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242066801 / 2 + 0.399 * 0.000968325801 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184891921 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484148252 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117648026 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242066801 / 1.414213562 := by gcongr
      _ ≤ (0.000068295664 : ℝ) := by norm_num

end BstLean.Part269.N13206

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13206
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) ≤ 1.47629E-7 := by
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13206 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13206 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13206 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184891921 : ℝ) ^ 2 + 0.000117648026 ^ 2 + 3 * 0.000068295664 ^ 2 +
        2 * 0.797885 * 0.000184891921 * 0.000117648026 + 2 * 0.000184891921 * 0.000068295664 +
        4 * 0.797885 * 0.000117648026 * 0.000068295664 := by gcongr
    _ ≤ (1.47629E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13206 BstLean.Part154.csC Θ ≤ 0.002525130521 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13206 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13206 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13206 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035110513892 * 1.47629E-7 / (0.000242066426 : ℝ) := by gcongr
    _ ≤ 0.002525130521 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13206 BstLean.Part154.csC Θ ≤ 0.002799877015 + 0.000638060935 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13206 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13206 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035110513892 : ℝ) * ((2 * Θ * 0.000242066801 +
        (6863 / 10000) * 0.000242066801 * 13206 * 0.000968325801) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002799877015 + 0.000638060935 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13206 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13206 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13206 0.011 Θ ∧ gammaRatio 13206 0.011 Θ ≤ 0.000083216307 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13206 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035110513892 : ℝ) * 0.525 / ((1 - 0.011) * 13206) := by gcongr
      _ ≤ (0.000083216307 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13206 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13206 0.011 Θ) :=
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
    badAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13206 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13206 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13206 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13206 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13206 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13206 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13206 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13206 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13206 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13206 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035110513892 : ℝ) * 13206 *
        (1.1283E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003117447781 + 0.003163191456 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13206

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13206
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13206 BstLean.Part154.csC) (piBar (rhoBar 13206 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13206 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13206 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13206 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13206 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13206 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13206 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13206 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13206 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13206 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13206 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051458203325 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13206) ≤ 0.010392142356 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13206 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035110513892)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010392142356 + 2 * 0.737676 / 13206) := by gcongr
    _ ≤ (0.051458203325 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13206 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13206

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13206
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525574337 : ℝ) ≤ plow 13206 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13206) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284723296)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325693524) : eMP 13206 0.011 xi bn ≤ 0.001141963286 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13206 : ℝ) * (1 - 0.011))) ≤ 0.000564693431 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325693524 / (13206 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564693431 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564693431 : ℝ) + 3.141593 * 0.052284723296 / (13206 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141963286 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284723296)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325693524) : PiBarMP 13206 12 0.011 xi bn ≤ 0.158101334265 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13206 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036410074485 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.283568372710 : ℝ) ≤ √((13206 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.917361612595 : ℝ) ≤ √(13206 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13206) ≤ 0.121238497537 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036410074485 + 0.052284723296 * 1.772454 / (2 * (114.283568372710 : ℝ))) * (1 + 0.001141963286) +
        8 / (13206 * 114.917361612595) + 0.121238497537 := by gcongr
    _ ≤ (0.158101334265 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284723296)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325693524) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280116733225) :
    parallelOracle 13206 0.011 xi bn cd ≤ 0.159054170486 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13206 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13206 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525574337 : ℝ) ≤ plow 13206 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.917361612595 : ℝ) ≤ √(13206 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280116733225 : ℝ) / (2 * 0.560525574337 * 114.917361612595)) * 0.158101334265 +
        0.280116733225 ^ 2 / (2 * 0.560525574337 * 114.917361612595) := by gcongr
    _ ≤ (0.159054170486 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284723296) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325693524)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280116733225) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13206 13206 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525574337 : ℝ) ≤ plow 13206 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.917361612595 : ℝ) ≤ √(13206 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13206 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13206 Θ 1.22 ≤ 0.011539600992 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.917361612595 := by gcongr <;> linarith
      _ ≤ (0.011539600992 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13206 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13206 13206 0.011 ≤ 0.008318037196 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13206 13206 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13206 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13206 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13206 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13206 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159054170486 + 0.011539600992 + (0.008318037196 : ℝ) *
        (1 + 2 * (0.280116733225 + 0.011539600992) / (0.560525574337 * 114.917361612595))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13206]

end BstLean.Part269.N13206

/-! The original eight local profiles supply actual 13206 moment certificates. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13206 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052284723296 ∧
    0 ≤ bN 13206 BstLean.Part154.csC (groupTheta g) ∧ bN 13206 BstLean.Part154.csC (groupTheta g) ≤ 0.001325693524 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13206 13206 0.011
      (momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13206 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13206 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13206 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228658529900 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13206 0.011
      (momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13206 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13206
/-! The actual computed-centre upper energy formula at 13206. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13206

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13206)
open BstLean.Part268 (cell13206)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084136795170
  | 2 => 0.085058904023
  | 3 => 0.085976272393
  | 4 => 0.086889639021
  | 5 => 0.087799916302
  | 6 => 0.088708218346
  | 7 => 0.089615892112
  | 8 => 0.090524551747
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13206 13206 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13206 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13206

/-! Actual upper energy certificates on all 43 source endpoints at 13206. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13206)
open BstLean.Part268 (cell13206)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13206 (gMinus 13206) (1 - (cell13206 i).lower) ≤ 1 ∧
    energyUpper 13206 (gMinus 13206) (BstLean.Part211.gPlus 13206)
      (finiteEnergy 13206 13206 0.011) (1 - (cell13206 i).lower) ≤
      (cell13206 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨10,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨11,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨12,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨13,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨14,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨15,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨16,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨17,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨18,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨19,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨20,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨21,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨22,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨23,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨24,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨25,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨26,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨27,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨28,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨29,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨30,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨31,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨32,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨33,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨34,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨35,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨36,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨37,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨38,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨39,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨40,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨41,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨42,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨43,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨44,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨45,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨46,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨47,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨48,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨49,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨50,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨51,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13206) (by norm_num)
        (q := 1 - (cell13206 ⟨52,by decide⟩).lower)
        (by norm_num [cell13206]) (by norm_num [cell13206])
      exact ⟨E.1,E.2.trans (by norm_num [cell13206])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13206

/-! Source-cell containment and simple scalar guards at 13206. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13206)
open BstLean.Part268 (cell13206)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13206 ⟨10,by decide⟩).lower ∧ (cell13206 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13206 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13206 ⟨11,by decide⟩).lower ∧ (cell13206 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13206 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13206 ⟨12,by decide⟩).lower ∧ (cell13206 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13206 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13206 ⟨13,by decide⟩).lower ∧ (cell13206 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13206 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13206 ⟨14,by decide⟩).lower ∧ (cell13206 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13206 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13206 ⟨15,by decide⟩).lower ∧ (cell13206 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13206 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13206 ⟨16,by decide⟩).lower ∧ (cell13206 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13206 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13206 ⟨17,by decide⟩).lower ∧ (cell13206 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13206 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13206 ⟨18,by decide⟩).lower ∧ (cell13206 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13206 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13206 ⟨19,by decide⟩).lower ∧ (cell13206 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13206 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13206 ⟨20,by decide⟩).lower ∧ (cell13206 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13206 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13206 ⟨21,by decide⟩).lower ∧ (cell13206 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13206 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13206 ⟨22,by decide⟩).lower ∧ (cell13206 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13206 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13206 ⟨23,by decide⟩).lower ∧ (cell13206 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13206 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13206 ⟨24,by decide⟩).lower ∧ (cell13206 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13206 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13206 ⟨25,by decide⟩).lower ∧ (cell13206 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13206 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13206 ⟨26,by decide⟩).lower ∧ (cell13206 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13206 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13206 ⟨27,by decide⟩).lower ∧ (cell13206 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13206 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13206 ⟨28,by decide⟩).lower ∧ (cell13206 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13206 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13206 ⟨29,by decide⟩).lower ∧ (cell13206 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13206 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13206 ⟨30,by decide⟩).lower ∧ (cell13206 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13206 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13206 ⟨31,by decide⟩).lower ∧ (cell13206 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13206 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13206 ⟨32,by decide⟩).lower ∧ (cell13206 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13206 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13206 ⟨33,by decide⟩).lower ∧ (cell13206 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13206 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13206 ⟨34,by decide⟩).lower ∧ (cell13206 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13206 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13206 ⟨35,by decide⟩).lower ∧ (cell13206 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13206 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13206 ⟨36,by decide⟩).lower ∧ (cell13206 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13206 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13206 ⟨37,by decide⟩).lower ∧ (cell13206 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13206 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13206 ⟨38,by decide⟩).lower ∧ (cell13206 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13206 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13206 ⟨39,by decide⟩).lower ∧ (cell13206 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13206 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13206 ⟨40,by decide⟩).lower ∧ (cell13206 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13206 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13206 ⟨41,by decide⟩).lower ∧ (cell13206 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13206 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13206 ⟨42,by decide⟩).lower ∧ (cell13206 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13206 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13206 ⟨43,by decide⟩).lower ∧ (cell13206 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13206 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13206 ⟨44,by decide⟩).lower ∧ (cell13206 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13206 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13206 ⟨45,by decide⟩).lower ∧ (cell13206 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13206 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13206 ⟨46,by decide⟩).lower ∧ (cell13206 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13206 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13206 ⟨47,by decide⟩).lower ∧ (cell13206 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13206 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13206 ⟨48,by decide⟩).lower ∧ (cell13206 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13206 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13206 ⟨49,by decide⟩).lower ∧ (cell13206 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13206 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13206 ⟨50,by decide⟩).lower ∧ (cell13206 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13206 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13206 ⟨51,by decide⟩).lower ∧ (cell13206 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13206 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13206 ⟨52,by decide⟩).lower ∧ (cell13206 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13206 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13206 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13206 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13206,cell13206,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13206 i).lower ∧
    (cell13206 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13206 i).upper ≤ (0.532 : ℝ) ∧
    (cell13206 i).centre ≤ (0.1 : ℝ) ∧ (cell13206 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13206 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13206 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13206

/-! The local source numeric instances at 13206 have no network premises. -/
namespace BstLean.Part269.N13206
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13206)
open BstLean.Part268 (cell13206)

noncomputable def sourceNumerics13206 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13206 (cell13206 i)
      scalarRow13206.M scalarRow13206.H scalarRow13206.xi := by
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
    energy_allowance := scalarRow13206.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13206]
    centre_nonneg := (scalarRow13206.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13206])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13206
/-! Actual 13207 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13207 ≤ (1.035109173161 : ℝ) := by
  have hr : (114.921712482889 : ℝ) ≤ √(13207 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.921712482889 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13207 13207 (11 / 1000) ≤
    (0.008317722277 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13207) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.921712482889 : ℝ) ≤ √(13207 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13207)
  have hdiv : K / √(13207 : ℝ) ≤ K / 114.921712482889 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.921712482889 ≤ (0.008317722277 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13207.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13207 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13207 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13207 := gPlus_lower 13207
end BstLean.Part269.N13207

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13207
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035109173160 : ℝ) ≤ wn 13207 := by
  have hn : √(13207 : ℝ) ≤ 114.921712482890 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13207 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.921712482890 ≤ 2 / √(13207 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242047784 : ℝ) ≤ rhoBar 13207 BstLean.Part154.csC ∧
    rhoBar 13207 BstLean.Part154.csC ≤ 0.000242048158 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035109173160 : ℝ) / (1.295212 * 13207) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035109173161 : ℝ) / (1.29521 * 13207) := by gcongr
      _ ≤ (0.000242048158 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13207 BstLean.Part154.csC) ≤ 0.000968251220 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13207 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) ≤ 0.000184877680 ∧
    cc1 (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) ≤ 0.000117638965 ∧
    cc2 (rhoBar 13207 BstLean.Part154.csC) ≤ 0.000068290404 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13207 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13207 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13207 BstLean.Part154.csC * nuR (rhoBar 13207 BstLean.Part154.csC)) ≤ 0.000484110963 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242048158 : ℝ) * 0.000968251220 := by gcongr
      _ ≤ (0.000484110963 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13207 BstLean.Part154.csC) * nuR (rhoBar 13207 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968251220 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13207 BstLean.Part154.csC) * rhoBar 13207 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242048158 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242048158 / 2 + 0.399 * 0.000968251220 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184877680 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484110963 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117638965 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242048158 / 1.414213562 := by gcongr
      _ ≤ (0.000068290404 : ℝ) := by norm_num

end BstLean.Part269.N13207

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13207
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) ≤ 1.47606E-7 := by
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13207 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13207 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13207 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184877680 : ℝ) ^ 2 + 0.000117638965 ^ 2 + 3 * 0.000068290404 ^ 2 +
        2 * 0.797885 * 0.000184877680 * 0.000117638965 + 2 * 0.000184877680 * 0.000068290404 +
        4 * 0.797885 * 0.000117638965 * 0.000068290404 := by gcongr
    _ ≤ (1.47606E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13207 BstLean.Part154.csC Θ ≤ 0.002524928295 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13207 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13207 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13207 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035109173161 * 1.47606E-7 / (0.000242047784 : ℝ) := by gcongr
    _ ≤ 0.002524928295 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13207 BstLean.Part154.csC Θ ≤ 0.002799654105 + 0.000638010967 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13207 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13207 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035109173161 : ℝ) * ((2 * Θ * 0.000242048158 +
        (6863 / 10000) * 0.000242048158 * 13207 * 0.000968251220) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002799654105 + 0.000638010967 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13207 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13207 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13207 0.011 Θ ∧ gammaRatio 13207 0.011 Θ ≤ 0.000083209898 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13207 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035109173161 : ℝ) * 0.525 / ((1 - 0.011) * 13207) := by gcongr
      _ ≤ (0.000083209898 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13207 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13207 0.011 Θ) :=
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
    badAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13207 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13207 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13207 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13207 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13207 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13207 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13207 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13207 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13207 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13207 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035109173161 : ℝ) * 13207 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003117224871 + 0.003162939262 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13207

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13207
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13207 BstLean.Part154.csC) (piBar (rhoBar 13207 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13207 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13207 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13207 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13207 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13207 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13207 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13207 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13207 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13207 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13207 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051456234430 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13207) ≤ 0.010391748916 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13207 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035109173161)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010391748916 + 2 * 0.737676 / 13207) := by gcongr
    _ ≤ (0.051456234430 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13207 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13207

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13207
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525616158 : ℝ) ≤ plow 13207 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13207) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284367984)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325587355) : eMP 13207 0.011 xi bn ≤ 0.001141874268 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13207 : ℝ) * (1 - 0.011))) ≤ 0.000564649441 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325587355 / (13207 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564649441 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564649441 : ℝ) + 3.141593 * 0.052284367984 / (13207 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141874268 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284367984)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325587355) : PiBarMP 13207 12 0.011 xi bn ≤ 0.158095262587 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13207 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036408616494 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.287895247047 : ℝ) ≤ √((13207 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.921712482889 : ℝ) ≤ √(13207 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13207) ≤ 0.121233907517 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036408616494 + 0.052284367984 * 1.772454 / (2 * (114.287895247047 : ℝ))) * (1 + 0.001141874268) +
        8 / (13207 * 114.921712482889) + 0.121233907517 := by gcongr
    _ ≤ (0.158095262587 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284367984)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325587355) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280113987380) :
    parallelOracle 13207 0.011 xi bn cd ≤ 0.159048034152 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13207 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13207 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525616158 : ℝ) ≤ plow 13207 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.921712482889 : ℝ) ≤ √(13207 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280113987380 : ℝ) / (2 * 0.560525616158 * 114.921712482889)) * 0.158095262587 +
        0.280113987380 ^ 2 / (2 * 0.560525616158 * 114.921712482889) := by gcongr
    _ ≤ (0.159048034152 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284367984) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325587355)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280113987380) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13207 13207 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525616158 : ℝ) ≤ plow 13207 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.921712482889 : ℝ) ≤ √(13207 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13207 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13207 Θ 1.22 ≤ 0.011539164109 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.921712482889 := by gcongr <;> linarith
      _ ≤ (0.011539164109 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13207 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13207 13207 0.011 ≤ 0.008317722277 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13207 13207 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13207 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13207 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13207 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13207 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159048034152 + 0.011539164109 + (0.008317722277 : ℝ) *
        (1 + 2 * (0.280113987380 + 0.011539164109) / (0.560525616158 * 114.921712482889))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13207]

end BstLean.Part269.N13207

/-! The original eight local profiles supply actual 13207 moment certificates. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13207 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052284367984 ∧
    0 ≤ bN 13207 BstLean.Part154.csC (groupTheta g) ∧ bN 13207 BstLean.Part154.csC (groupTheta g) ≤ 0.001325587355 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13207 13207 0.011
      (momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13207 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13207 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13207 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228657752950 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13207 0.011
      (momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13207 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13207
/-! The actual computed-centre upper energy formula at 13207. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13207

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13207)
open BstLean.Part268 (cell13207)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084134328705
  | 2 => 0.085056408171
  | 3 => 0.085973743143
  | 4 => 0.086887071393
  | 5 => 0.087797304167
  | 6 => 0.088705554215
  | 7 => 0.089613166904
  | 8 => 0.090521754526
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13207 13207 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13207 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13207

/-! Actual upper energy certificates on all 43 source endpoints at 13207. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13207)
open BstLean.Part268 (cell13207)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13207 (gMinus 13207) (1 - (cell13207 i).lower) ≤ 1 ∧
    energyUpper 13207 (gMinus 13207) (BstLean.Part211.gPlus 13207)
      (finiteEnergy 13207 13207 0.011) (1 - (cell13207 i).lower) ≤
      (cell13207 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨10,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨11,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨12,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨13,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨14,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨15,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨16,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨17,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨18,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨19,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨20,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨21,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨22,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨23,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨24,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨25,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨26,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨27,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨28,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨29,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨30,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨31,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨32,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨33,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨34,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨35,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨36,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨37,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨38,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨39,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨40,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨41,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨42,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨43,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨44,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨45,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨46,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨47,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨48,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨49,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨50,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨51,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13207) (by norm_num)
        (q := 1 - (cell13207 ⟨52,by decide⟩).lower)
        (by norm_num [cell13207]) (by norm_num [cell13207])
      exact ⟨E.1,E.2.trans (by norm_num [cell13207])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13207

/-! Source-cell containment and simple scalar guards at 13207. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13207)
open BstLean.Part268 (cell13207)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13207 ⟨10,by decide⟩).lower ∧ (cell13207 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13207 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13207 ⟨11,by decide⟩).lower ∧ (cell13207 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13207 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13207 ⟨12,by decide⟩).lower ∧ (cell13207 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13207 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13207 ⟨13,by decide⟩).lower ∧ (cell13207 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13207 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13207 ⟨14,by decide⟩).lower ∧ (cell13207 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13207 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13207 ⟨15,by decide⟩).lower ∧ (cell13207 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13207 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13207 ⟨16,by decide⟩).lower ∧ (cell13207 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13207 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13207 ⟨17,by decide⟩).lower ∧ (cell13207 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13207 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13207 ⟨18,by decide⟩).lower ∧ (cell13207 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13207 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13207 ⟨19,by decide⟩).lower ∧ (cell13207 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13207 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13207 ⟨20,by decide⟩).lower ∧ (cell13207 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13207 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13207 ⟨21,by decide⟩).lower ∧ (cell13207 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13207 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13207 ⟨22,by decide⟩).lower ∧ (cell13207 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13207 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13207 ⟨23,by decide⟩).lower ∧ (cell13207 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13207 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13207 ⟨24,by decide⟩).lower ∧ (cell13207 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13207 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13207 ⟨25,by decide⟩).lower ∧ (cell13207 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13207 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13207 ⟨26,by decide⟩).lower ∧ (cell13207 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13207 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13207 ⟨27,by decide⟩).lower ∧ (cell13207 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13207 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13207 ⟨28,by decide⟩).lower ∧ (cell13207 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13207 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13207 ⟨29,by decide⟩).lower ∧ (cell13207 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13207 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13207 ⟨30,by decide⟩).lower ∧ (cell13207 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13207 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13207 ⟨31,by decide⟩).lower ∧ (cell13207 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13207 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13207 ⟨32,by decide⟩).lower ∧ (cell13207 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13207 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13207 ⟨33,by decide⟩).lower ∧ (cell13207 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13207 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13207 ⟨34,by decide⟩).lower ∧ (cell13207 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13207 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13207 ⟨35,by decide⟩).lower ∧ (cell13207 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13207 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13207 ⟨36,by decide⟩).lower ∧ (cell13207 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13207 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13207 ⟨37,by decide⟩).lower ∧ (cell13207 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13207 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13207 ⟨38,by decide⟩).lower ∧ (cell13207 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13207 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13207 ⟨39,by decide⟩).lower ∧ (cell13207 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13207 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13207 ⟨40,by decide⟩).lower ∧ (cell13207 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13207 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13207 ⟨41,by decide⟩).lower ∧ (cell13207 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13207 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13207 ⟨42,by decide⟩).lower ∧ (cell13207 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13207 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13207 ⟨43,by decide⟩).lower ∧ (cell13207 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13207 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13207 ⟨44,by decide⟩).lower ∧ (cell13207 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13207 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13207 ⟨45,by decide⟩).lower ∧ (cell13207 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13207 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13207 ⟨46,by decide⟩).lower ∧ (cell13207 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13207 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13207 ⟨47,by decide⟩).lower ∧ (cell13207 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13207 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13207 ⟨48,by decide⟩).lower ∧ (cell13207 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13207 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13207 ⟨49,by decide⟩).lower ∧ (cell13207 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13207 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13207 ⟨50,by decide⟩).lower ∧ (cell13207 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13207 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13207 ⟨51,by decide⟩).lower ∧ (cell13207 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13207 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13207 ⟨52,by decide⟩).lower ∧ (cell13207 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13207 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13207 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13207 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13207,cell13207,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13207 i).lower ∧
    (cell13207 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13207 i).upper ≤ (0.532 : ℝ) ∧
    (cell13207 i).centre ≤ (0.1 : ℝ) ∧ (cell13207 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13207 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13207 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13207

/-! The local source numeric instances at 13207 have no network premises. -/
namespace BstLean.Part269.N13207
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13207)
open BstLean.Part268 (cell13207)

noncomputable def sourceNumerics13207 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13207 (cell13207 i)
      scalarRow13207.M scalarRow13207.H scalarRow13207.xi := by
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
    energy_allowance := scalarRow13207.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13207]
    centre_nonneg := (scalarRow13207.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13207])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13207
/-! Actual 13208 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13208 ≤ (1.035107832583 : ℝ) := by
  have hr : (114.926063188469 : ℝ) ≤ √(13208 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.926063188469 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13208 13208 (11 / 1000) ≤
    (0.008317407394 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13208) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.926063188469 : ℝ) ≤ √(13208 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13208)
  have hdiv : K / √(13208 : ℝ) ≤ K / 114.926063188469 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.926063188469 ≤ (0.008317407394 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13208.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13208 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13208 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13208 := gPlus_lower 13208
end BstLean.Part269.N13208

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13208
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035107832582 : ℝ) ≤ wn 13208 := by
  have hn : √(13208 : ℝ) ≤ 114.926063188470 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13208 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.926063188470 ≤ 2 / √(13208 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242029144 : ℝ) ≤ rhoBar 13208 BstLean.Part154.csC ∧
    rhoBar 13208 BstLean.Part154.csC ≤ 0.000242029519 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035107832582 : ℝ) / (1.295212 * 13208) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035107832583 : ℝ) / (1.29521 * 13208) := by gcongr
      _ ≤ (0.000242029519 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13208 BstLean.Part154.csC) ≤ 0.000968176655 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13208 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) ≤ 0.000184863443 ∧
    cc1 (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) ≤ 0.000117629905 ∧
    cc2 (rhoBar 13208 BstLean.Part154.csC) ≤ 0.000068285145 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13208 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13208 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13208 BstLean.Part154.csC * nuR (rhoBar 13208 BstLean.Part154.csC)) ≤ 0.000484073683 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242029519 : ℝ) * 0.000968176655 := by gcongr
      _ ≤ (0.000484073683 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13208 BstLean.Part154.csC) * nuR (rhoBar 13208 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968176655 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13208 BstLean.Part154.csC) * rhoBar 13208 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242029519 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242029519 / 2 + 0.399 * 0.000968176655 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184863443 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484073683 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117629905 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242029519 / 1.414213562 := by gcongr
      _ ≤ (0.000068285145 : ℝ) := by norm_num

end BstLean.Part269.N13208

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13208
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) ≤ 1.47584E-7 := by
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13208 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13208 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13208 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184863443 : ℝ) ^ 2 + 0.000117629905 ^ 2 + 3 * 0.000068285145 ^ 2 +
        2 * 0.797885 * 0.000184863443 * 0.000117629905 + 2 * 0.000184863443 * 0.000068285145 +
        4 * 0.797885 * 0.000117629905 * 0.000068285145 := by gcongr
    _ ≤ (1.47584E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13208 BstLean.Part154.csC Θ ≤ 0.002524743126 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13208 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13208 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13208 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035107832583 * 1.47584E-7 / (0.000242029144 : ℝ) := by gcongr
    _ ≤ 0.002524743126 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13208 BstLean.Part154.csC Θ ≤ 0.002799431257 + 0.000637961011 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13208 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13208 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035107832583 : ℝ) * ((2 * Θ * 0.000242029519 +
        (6863 / 10000) * 0.000242029519 * 13208 * 0.000968176655) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002799431257 + 0.000637961011 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13208 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13208 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13208 0.011 Θ ∧ gammaRatio 13208 0.011 Θ ≤ 0.000083203490 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13208 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035107832583 : ℝ) * 0.525 / ((1 - 0.011) * 13208) := by gcongr
      _ ≤ (0.000083203490 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13208 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13208 0.011 Θ) :=
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
    badAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13208 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13208 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13208 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13208 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13208 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13208 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13208 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13208 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13208 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13208 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035107832583 : ℝ) * 13208 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003117002023 + 0.003162704137 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13208

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13208
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13208 BstLean.Part154.csC) (piBar (rhoBar 13208 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13208 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13208 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13208 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13208 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13208 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13208 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13208 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13208 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13208 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13208 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051454265757 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13208) ≤ 0.010391355520 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13208 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035107832583)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010391355520 + 2 * 0.737676 / 13208) := by gcongr
    _ ≤ (0.051454265757 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13208 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13208

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13208
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525657972 : ℝ) ≤ plow 13208 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13208) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284021695)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325490142) : eMP 13208 0.011 xi bn ≤ 0.001141789073 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13208 : ℝ) * (1 - 0.011))) ≤ 0.000564607361 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325490142 / (13208 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564607361 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564607361 : ℝ) + 3.141593 * 0.052284021695 / (13208 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141789073 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284021695)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325490142) : PiBarMP 13208 12 0.011 xi bn ≤ 0.158089314724 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13208 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036407281443 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.292221957576 : ℝ) ≤ √((13208 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.926063188469 : ℝ) ≤ √(13208 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13208) ≤ 0.121229318018 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036407281443 + 0.052284021695 * 1.772454 / (2 * (114.292221957576 : ℝ))) * (1 + 0.001141789073) +
        8 / (13208 * 114.926063188469) + 0.121229318018 := by gcongr
    _ ≤ (0.158089314724 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284021695)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325490142) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280111261485) :
    parallelOracle 13208 0.011 xi bn cd ≤ 0.159042022020 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13208 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13208 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525657972 : ℝ) ≤ plow 13208 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.926063188469 : ℝ) ≤ √(13208 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280111261485 : ℝ) / (2 * 0.560525657972 * 114.926063188469)) * 0.158089314724 +
        0.280111261485 ^ 2 / (2 * 0.560525657972 * 114.926063188469) := by gcongr
    _ ≤ (0.159042022020 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052284021695) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325490142)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280111261485) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13208 13208 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525657972 : ℝ) ≤ plow 13208 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.926063188469 : ℝ) ≤ √(13208 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13208 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13208 Θ 1.22 ≤ 0.011538727276 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.926063188469 := by gcongr <;> linarith
      _ ≤ (0.011538727276 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13208 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13208 13208 0.011 ≤ 0.008317407394 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13208 13208 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13208 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13208 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13208 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13208 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159042022020 + 0.011538727276 + (0.008317407394 : ℝ) *
        (1 + 2 * (0.280111261485 + 0.011538727276) / (0.560525657972 * 114.926063188469))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13208]

end BstLean.Part269.N13208

/-! The original eight local profiles supply actual 13208 moment certificates. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13208 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052284021695 ∧
    0 ≤ bN 13208 BstLean.Part154.csC (groupTheta g) ∧ bN 13208 BstLean.Part154.csC (groupTheta g) ≤ 0.001325490142 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13208 13208 0.011
      (momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13208 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13208 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13208 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228656995728 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13208 0.011
      (momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13208 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13208
/-! The actual computed-centre upper energy formula at 13208. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13208

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13208)
open BstLean.Part268 (cell13208)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084131862912
  | 2 => 0.085053913012
  | 3 => 0.085971214613
  | 4 => 0.086884504519
  | 5 => 0.087794692827
  | 6 => 0.088702890930
  | 7 => 0.089610442604
  | 8 => 0.090518958286
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13208 13208 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13208 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13208

/-! Actual upper energy certificates on all 43 source endpoints at 13208. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13208)
open BstLean.Part268 (cell13208)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13208 (gMinus 13208) (1 - (cell13208 i).lower) ≤ 1 ∧
    energyUpper 13208 (gMinus 13208) (BstLean.Part211.gPlus 13208)
      (finiteEnergy 13208 13208 0.011) (1 - (cell13208 i).lower) ≤
      (cell13208 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨10,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨11,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨12,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨13,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨14,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨15,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨16,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨17,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨18,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨19,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨20,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨21,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨22,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨23,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨24,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨25,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨26,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨27,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨28,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨29,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨30,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨31,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨32,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨33,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨34,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨35,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨36,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨37,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨38,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨39,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨40,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨41,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨42,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨43,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨44,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨45,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨46,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨47,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨48,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨49,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨50,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨51,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13208) (by norm_num)
        (q := 1 - (cell13208 ⟨52,by decide⟩).lower)
        (by norm_num [cell13208]) (by norm_num [cell13208])
      exact ⟨E.1,E.2.trans (by norm_num [cell13208])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13208

/-! Source-cell containment and simple scalar guards at 13208. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13208)
open BstLean.Part268 (cell13208)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13208 ⟨10,by decide⟩).lower ∧ (cell13208 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13208 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13208 ⟨11,by decide⟩).lower ∧ (cell13208 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13208 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13208 ⟨12,by decide⟩).lower ∧ (cell13208 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13208 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13208 ⟨13,by decide⟩).lower ∧ (cell13208 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13208 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13208 ⟨14,by decide⟩).lower ∧ (cell13208 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13208 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13208 ⟨15,by decide⟩).lower ∧ (cell13208 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13208 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13208 ⟨16,by decide⟩).lower ∧ (cell13208 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13208 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13208 ⟨17,by decide⟩).lower ∧ (cell13208 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13208 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13208 ⟨18,by decide⟩).lower ∧ (cell13208 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13208 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13208 ⟨19,by decide⟩).lower ∧ (cell13208 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13208 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13208 ⟨20,by decide⟩).lower ∧ (cell13208 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13208 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13208 ⟨21,by decide⟩).lower ∧ (cell13208 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13208 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13208 ⟨22,by decide⟩).lower ∧ (cell13208 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13208 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13208 ⟨23,by decide⟩).lower ∧ (cell13208 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13208 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13208 ⟨24,by decide⟩).lower ∧ (cell13208 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13208 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13208 ⟨25,by decide⟩).lower ∧ (cell13208 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13208 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13208 ⟨26,by decide⟩).lower ∧ (cell13208 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13208 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13208 ⟨27,by decide⟩).lower ∧ (cell13208 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13208 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13208 ⟨28,by decide⟩).lower ∧ (cell13208 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13208 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13208 ⟨29,by decide⟩).lower ∧ (cell13208 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13208 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13208 ⟨30,by decide⟩).lower ∧ (cell13208 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13208 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13208 ⟨31,by decide⟩).lower ∧ (cell13208 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13208 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13208 ⟨32,by decide⟩).lower ∧ (cell13208 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13208 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13208 ⟨33,by decide⟩).lower ∧ (cell13208 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13208 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13208 ⟨34,by decide⟩).lower ∧ (cell13208 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13208 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13208 ⟨35,by decide⟩).lower ∧ (cell13208 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13208 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13208 ⟨36,by decide⟩).lower ∧ (cell13208 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13208 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13208 ⟨37,by decide⟩).lower ∧ (cell13208 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13208 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13208 ⟨38,by decide⟩).lower ∧ (cell13208 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13208 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13208 ⟨39,by decide⟩).lower ∧ (cell13208 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13208 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13208 ⟨40,by decide⟩).lower ∧ (cell13208 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13208 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13208 ⟨41,by decide⟩).lower ∧ (cell13208 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13208 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13208 ⟨42,by decide⟩).lower ∧ (cell13208 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13208 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13208 ⟨43,by decide⟩).lower ∧ (cell13208 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13208 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13208 ⟨44,by decide⟩).lower ∧ (cell13208 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13208 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13208 ⟨45,by decide⟩).lower ∧ (cell13208 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13208 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13208 ⟨46,by decide⟩).lower ∧ (cell13208 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13208 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13208 ⟨47,by decide⟩).lower ∧ (cell13208 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13208 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13208 ⟨48,by decide⟩).lower ∧ (cell13208 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13208 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13208 ⟨49,by decide⟩).lower ∧ (cell13208 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13208 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13208 ⟨50,by decide⟩).lower ∧ (cell13208 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13208 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13208 ⟨51,by decide⟩).lower ∧ (cell13208 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13208 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13208 ⟨52,by decide⟩).lower ∧ (cell13208 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13208 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13208 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13208 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13208,cell13208,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13208 i).lower ∧
    (cell13208 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13208 i).upper ≤ (0.532 : ℝ) ∧
    (cell13208 i).centre ≤ (0.1 : ℝ) ∧ (cell13208 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13208 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13208 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13208

/-! The local source numeric instances at 13208 have no network premises. -/
namespace BstLean.Part269.N13208
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13208)
open BstLean.Part268 (cell13208)

noncomputable def sourceNumerics13208 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13208 (cell13208 i)
      scalarRow13208.M scalarRow13208.H scalarRow13208.xi := by
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
    energy_allowance := scalarRow13208.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13208]
    centre_nonneg := (scalarRow13208.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13208])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13208
/-! Actual 13209 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13209 ≤ (1.035106492159 : ℝ) := by
  have hr : (114.930413729351 : ℝ) ≤ √(13209 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.930413729351 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13209 13209 (11 / 1000) ≤
    (0.008317092548 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13209) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.930413729351 : ℝ) ≤ √(13209 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13209)
  have hdiv : K / √(13209 : ℝ) ≤ K / 114.930413729351 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.930413729351 ≤ (0.008317092548 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13209.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13209 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13209 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13209 := gPlus_lower 13209
end BstLean.Part269.N13209

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13209
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035106492158 : ℝ) ≤ wn 13209 := by
  have hn : √(13209 : ℝ) ≤ 114.930413729352 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13209 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.930413729352 ≤ 2 / √(13209 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242010508 : ℝ) ≤ rhoBar 13209 BstLean.Part154.csC ∧
    rhoBar 13209 BstLean.Part154.csC ≤ 0.000242010883 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035106492158 : ℝ) / (1.295212 * 13209) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035106492159 : ℝ) / (1.29521 * 13209) := by gcongr
      _ ≤ (0.000242010883 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13209 BstLean.Part154.csC) ≤ 0.000968102102 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13209 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) ≤ 0.000184849208 ∧
    cc1 (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) ≤ 0.000117620848 ∧
    cc2 (rhoBar 13209 BstLean.Part154.csC) ≤ 0.000068279888 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13209 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13209 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13209 BstLean.Part154.csC * nuR (rhoBar 13209 BstLean.Part154.csC)) ≤ 0.000484036409 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242010883 : ℝ) * 0.000968102102 := by gcongr
      _ ≤ (0.000484036409 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13209 BstLean.Part154.csC) * nuR (rhoBar 13209 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968102102 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13209 BstLean.Part154.csC) * rhoBar 13209 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242010883 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242010883 / 2 + 0.399 * 0.000968102102 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184849208 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484036409 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117620848 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242010883 / 1.414213562 := by gcongr
      _ ≤ (0.000068279888 : ℝ) := by norm_num

end BstLean.Part269.N13209

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13209
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) ≤ 1.47561E-7 := by
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13209 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13209 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13209 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184849208 : ℝ) ^ 2 + 0.000117620848 ^ 2 + 3 * 0.000068279888 ^ 2 +
        2 * 0.797885 * 0.000184849208 * 0.000117620848 + 2 * 0.000184849208 * 0.000068279888 +
        4 * 0.797885 * 0.000117620848 * 0.000068279888 := by gcongr
    _ ≤ (1.47561E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13209 BstLean.Part154.csC Θ ≤ 0.002524540779 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13209 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13209 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13209 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035106492159 * 1.47561E-7 / (0.000242010508 : ℝ) := by gcongr
    _ ≤ 0.002524540779 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13209 BstLean.Part154.csC Θ ≤ 0.002799208446 + 0.000637911063 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13209 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13209 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035106492159 : ℝ) * ((2 * Θ * 0.000242010883 +
        (6863 / 10000) * 0.000242010883 * 13209 * 0.000968102102) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002799208446 + 0.000637911063 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13209 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13209 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13209 0.011 Θ ∧ gammaRatio 13209 0.011 Θ ≤ 0.000083197084 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13209 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035106492159 : ℝ) * 0.525 / ((1 - 0.011) * 13209) := by gcongr
      _ ≤ (0.000083197084 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13209 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13209 0.011 Θ) :=
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
    badAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13209 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13209 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13209 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13209 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13209 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13209 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13209 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13209 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13209 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13209 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035106492159 : ℝ) * 13209 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003116779212 + 0.003162451842 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13209

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13209
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13209 BstLean.Part154.csC) (piBar (rhoBar 13209 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13209 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13209 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13209 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13209 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13209 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13209 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13209 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13209 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13209 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13209 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051452297310 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13209) ≤ 0.010390962169 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13209 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035106492159)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010390962169 + 2 * 0.737676 / 13209) := by gcongr
    _ ≤ (0.051452297310 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13209 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13209

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13209
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525699780 : ℝ) ≤ plow 13209 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13209) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283666430)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325383909) : eMP 13209 0.011 xi bn ≤ 0.001141700039 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13209 : ℝ) * (1 - 0.011))) ≤ 0.000564563363 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325383909 / (13209 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564563363 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564563363 : ℝ) + 3.141593 * 0.052283666430 / (13209 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141700039 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283666430)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325383909) : PiBarMP 13209 12 0.011 xi bn ≤ 0.158083243101 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13209 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036405822461 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.296548504318 : ℝ) ≤ √((13209 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.930413729351 : ℝ) ≤ √(13209 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13209) ≤ 0.121224729040 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036405822461 + 0.052283666430 * 1.772454 / (2 * (114.296548504318 : ℝ))) * (1 + 0.001141700039) +
        8 / (13209 * 114.930413729351) + 0.121224729040 := by gcongr
    _ ≤ (0.158083243101 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283666430)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325383909) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280108516185) :
    parallelOracle 13209 0.011 xi bn cd ≤ 0.159035885757 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13209 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13209 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525699780 : ℝ) ≤ plow 13209 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.930413729351 : ℝ) ≤ √(13209 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280108516185 : ℝ) / (2 * 0.560525699780 * 114.930413729351)) * 0.158083243101 +
        0.280108516185 ^ 2 / (2 * 0.560525699780 * 114.930413729351) := by gcongr
    _ ≤ (0.159035885757 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283666430) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325383909)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280108516185) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13209 13209 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525699780 : ℝ) ≤ plow 13209 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.930413729351 : ℝ) ≤ √(13209 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13209 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13209 Θ 1.22 ≤ 0.011538290493 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.930413729351 := by gcongr <;> linarith
      _ ≤ (0.011538290493 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13209 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13209 13209 0.011 ≤ 0.008317092548 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13209 13209 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13209 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13209 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13209 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13209 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159035885757 + 0.011538290493 + (0.008317092548 : ℝ) *
        (1 + 2 * (0.280108516185 + 0.011538290493) / (0.560525699780 * 114.930413729351))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13209]

end BstLean.Part269.N13209

/-! The original eight local profiles supply actual 13209 moment certificates. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13209 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052283666430 ∧
    0 ≤ bN 13209 BstLean.Part154.csC (groupTheta g) ∧ bN 13209 BstLean.Part154.csC (groupTheta g) ≤ 0.001325383909 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13209 13209 0.011
      (momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13209 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13209 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13209 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228656218875 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13209 0.011
      (momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13209 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13209
/-! The actual computed-centre upper energy formula at 13209. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13209

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13209)
open BstLean.Part268 (cell13209)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084129397790
  | 2 => 0.085051418546
  | 3 => 0.085968686803
  | 4 => 0.086881938399
  | 5 => 0.087792082282
  | 6 => 0.088700228490
  | 7 => 0.089607719210
  | 8 => 0.090516163029
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13209 13209 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13209 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13209

/-! Actual upper energy certificates on all 43 source endpoints at 13209. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13209)
open BstLean.Part268 (cell13209)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13209 (gMinus 13209) (1 - (cell13209 i).lower) ≤ 1 ∧
    energyUpper 13209 (gMinus 13209) (BstLean.Part211.gPlus 13209)
      (finiteEnergy 13209 13209 0.011) (1 - (cell13209 i).lower) ≤
      (cell13209 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨10,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨11,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨12,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨13,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨14,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨15,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨16,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨17,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨18,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨19,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨20,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨21,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨22,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨23,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨24,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨25,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨26,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨27,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨28,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨29,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨30,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨31,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨32,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨33,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨34,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨35,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨36,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨37,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨38,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨39,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨40,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨41,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨42,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨43,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨44,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨45,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨46,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨47,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨48,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨49,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨50,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨51,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13209) (by norm_num)
        (q := 1 - (cell13209 ⟨52,by decide⟩).lower)
        (by norm_num [cell13209]) (by norm_num [cell13209])
      exact ⟨E.1,E.2.trans (by norm_num [cell13209])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13209

/-! Source-cell containment and simple scalar guards at 13209. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13209)
open BstLean.Part268 (cell13209)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13209 ⟨10,by decide⟩).lower ∧ (cell13209 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13209 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13209 ⟨11,by decide⟩).lower ∧ (cell13209 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13209 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13209 ⟨12,by decide⟩).lower ∧ (cell13209 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13209 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13209 ⟨13,by decide⟩).lower ∧ (cell13209 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13209 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13209 ⟨14,by decide⟩).lower ∧ (cell13209 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13209 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13209 ⟨15,by decide⟩).lower ∧ (cell13209 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13209 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13209 ⟨16,by decide⟩).lower ∧ (cell13209 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13209 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13209 ⟨17,by decide⟩).lower ∧ (cell13209 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13209 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13209 ⟨18,by decide⟩).lower ∧ (cell13209 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13209 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13209 ⟨19,by decide⟩).lower ∧ (cell13209 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13209 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13209 ⟨20,by decide⟩).lower ∧ (cell13209 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13209 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13209 ⟨21,by decide⟩).lower ∧ (cell13209 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13209 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13209 ⟨22,by decide⟩).lower ∧ (cell13209 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13209 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13209 ⟨23,by decide⟩).lower ∧ (cell13209 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13209 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13209 ⟨24,by decide⟩).lower ∧ (cell13209 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13209 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13209 ⟨25,by decide⟩).lower ∧ (cell13209 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13209 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13209 ⟨26,by decide⟩).lower ∧ (cell13209 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13209 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13209 ⟨27,by decide⟩).lower ∧ (cell13209 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13209 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13209 ⟨28,by decide⟩).lower ∧ (cell13209 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13209 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13209 ⟨29,by decide⟩).lower ∧ (cell13209 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13209 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13209 ⟨30,by decide⟩).lower ∧ (cell13209 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13209 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13209 ⟨31,by decide⟩).lower ∧ (cell13209 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13209 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13209 ⟨32,by decide⟩).lower ∧ (cell13209 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13209 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13209 ⟨33,by decide⟩).lower ∧ (cell13209 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13209 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13209 ⟨34,by decide⟩).lower ∧ (cell13209 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13209 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13209 ⟨35,by decide⟩).lower ∧ (cell13209 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13209 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13209 ⟨36,by decide⟩).lower ∧ (cell13209 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13209 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13209 ⟨37,by decide⟩).lower ∧ (cell13209 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13209 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13209 ⟨38,by decide⟩).lower ∧ (cell13209 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13209 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13209 ⟨39,by decide⟩).lower ∧ (cell13209 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13209 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13209 ⟨40,by decide⟩).lower ∧ (cell13209 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13209 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13209 ⟨41,by decide⟩).lower ∧ (cell13209 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13209 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13209 ⟨42,by decide⟩).lower ∧ (cell13209 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13209 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13209 ⟨43,by decide⟩).lower ∧ (cell13209 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13209 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13209 ⟨44,by decide⟩).lower ∧ (cell13209 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13209 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13209 ⟨45,by decide⟩).lower ∧ (cell13209 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13209 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13209 ⟨46,by decide⟩).lower ∧ (cell13209 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13209 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13209 ⟨47,by decide⟩).lower ∧ (cell13209 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13209 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13209 ⟨48,by decide⟩).lower ∧ (cell13209 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13209 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13209 ⟨49,by decide⟩).lower ∧ (cell13209 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13209 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13209 ⟨50,by decide⟩).lower ∧ (cell13209 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13209 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13209 ⟨51,by decide⟩).lower ∧ (cell13209 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13209 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13209 ⟨52,by decide⟩).lower ∧ (cell13209 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13209 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13209 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13209 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13209,cell13209,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13209 i).lower ∧
    (cell13209 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13209 i).upper ≤ (0.532 : ℝ) ∧
    (cell13209 i).centre ≤ (0.1 : ℝ) ∧ (cell13209 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13209 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13209 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13209

/-! The local source numeric instances at 13209 have no network premises. -/
namespace BstLean.Part269.N13209
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13209)
open BstLean.Part268 (cell13209)

noncomputable def sourceNumerics13209 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13209 (cell13209 i)
      scalarRow13209.M scalarRow13209.H scalarRow13209.xi := by
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
    energy_allowance := scalarRow13209.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13209]
    centre_nonneg := (scalarRow13209.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13209])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13209
/-! Actual 13210 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13210 ≤ (1.035105151887 : ℝ) := by
  have hr : (114.934764105556 : ℝ) ≤ √(13210 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.934764105556 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13210 13210 (11 / 1000) ≤
    (0.008316777736 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13210) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.934764105556 : ℝ) ≤ √(13210 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13210)
  have hdiv : K / √(13210 : ℝ) ≤ K / 114.934764105556 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.934764105556 ≤ (0.008316777736 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13210.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13210 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13210 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13210 := gPlus_lower 13210
end BstLean.Part269.N13210

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13210
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035105151886 : ℝ) ≤ wn 13210 := by
  have hn : √(13210 : ℝ) ≤ 114.934764105557 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13210 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.934764105557 ≤ 2 / √(13210 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241991874 : ℝ) ≤ rhoBar 13210 BstLean.Part154.csC ∧
    rhoBar 13210 BstLean.Part154.csC ≤ 0.000241992249 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035105151886 : ℝ) / (1.295212 * 13210) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035105151887 : ℝ) / (1.29521 * 13210) := by gcongr
      _ ≤ (0.000241992249 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13210 BstLean.Part154.csC) ≤ 0.000968027557 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13210 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) ≤ 0.000184834975 ∧
    cc1 (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) ≤ 0.000117611791 ∧
    cc2 (rhoBar 13210 BstLean.Part154.csC) ≤ 0.000068274630 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13210 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13210 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13210 BstLean.Part154.csC * nuR (rhoBar 13210 BstLean.Part154.csC)) ≤ 0.000483999139 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241992249 : ℝ) * 0.000968027557 := by gcongr
      _ ≤ (0.000483999139 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13210 BstLean.Part154.csC) * nuR (rhoBar 13210 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968027557 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13210 BstLean.Part154.csC) * rhoBar 13210 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241992249 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241992249 / 2 + 0.399 * 0.000968027557 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184834975 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483999139 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117611791 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241992249 / 1.414213562 := by gcongr
      _ ≤ (0.000068274630 : ℝ) := by norm_num

end BstLean.Part269.N13210

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13210
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) ≤ 1.47538E-7 := by
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13210 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13210 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13210 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184834975 : ℝ) ^ 2 + 0.000117611791 ^ 2 + 3 * 0.000068274630 ^ 2 +
        2 * 0.797885 * 0.000184834975 * 0.000117611791 + 2 * 0.000184834975 * 0.000068274630 +
        4 * 0.797885 * 0.000117611791 * 0.000068274630 := by gcongr
    _ ≤ (1.47538E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13210 BstLean.Part154.csC Θ ≤ 0.002524338382 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13210 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13210 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13210 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035105151887 * 1.47538E-7 / (0.000241991874 : ℝ) := by gcongr
    _ ≤ 0.002524338382 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13210 BstLean.Part154.csC Θ ≤ 0.002798985651 + 0.000637861120 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13210 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13210 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035105151887 : ℝ) * ((2 * Θ * 0.000241992249 +
        (6863 / 10000) * 0.000241992249 * 13210 * 0.000968027557) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002798985651 + 0.000637861120 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13210 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13210 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13210 0.011 Θ ∧ gammaRatio 13210 0.011 Θ ≤ 0.000083190678 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13210 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035105151887 : ℝ) * 0.525 / ((1 - 0.011) * 13210) := by gcongr
      _ ≤ (0.000083190678 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13210 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13210 0.011 Θ) :=
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
    badAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13210 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13210 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13210 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13210 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13210 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13210 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13210 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13210 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13210 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13210 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035105151887 : ℝ) * 13210 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003116556417 + 0.003162199502 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13210

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13210
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13210 BstLean.Part154.csC) (piBar (rhoBar 13210 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13210 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13210 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13210 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13210 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13210 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13210 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13210 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13210 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13210 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13210 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051450329085 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13210) ≤ 0.010390568862 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13210 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035105151887)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010390568862 + 2 * 0.737676 / 13210) := by gcongr
    _ ≤ (0.051450329085 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13210 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13210

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13210
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525741582 : ℝ) ≤ plow 13210 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13210) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283311156)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325277651) : eMP 13210 0.011 xi bn ≤ 0.001141611004 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13210 : ℝ) * (1 - 0.011))) ≤ 0.000564519364 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325277651 / (13210 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564519364 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564519364 : ℝ) + 3.141593 * 0.052283311156 / (13210 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141611004 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283311156)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325277651) : PiBarMP 13210 12 0.011 xi bn ≤ 0.158077171599 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13210 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036404363077 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.300874887290 : ℝ) ≤ √((13210 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.934764105556 : ℝ) ≤ √(13210 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13210) ≤ 0.121220140584 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036404363077 + 0.052283311156 * 1.772454 / (2 * (114.300874887290 : ℝ))) * (1 + 0.001141611004) +
        8 / (13210 * 114.934764105556) + 0.121220140584 := by gcongr
    _ ≤ (0.158077171599 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283311156)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325277651) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280105771085) :
    parallelOracle 13210 0.011 xi bn cd ≤ 0.159029749623 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13210 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13210 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525741582 : ℝ) ≤ plow 13210 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.934764105556 : ℝ) ≤ √(13210 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280105771085 : ℝ) / (2 * 0.560525741582 * 114.934764105556)) * 0.158077171599 +
        0.280105771085 ^ 2 / (2 * 0.560525741582 * 114.934764105556) := by gcongr
    _ ≤ (0.159029749623 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052283311156) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325277651)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280105771085) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13210 13210 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525741582 : ℝ) ≤ plow 13210 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.934764105556 : ℝ) ≤ √(13210 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13210 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13210 Θ 1.22 ≤ 0.011537853759 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.934764105556 := by gcongr <;> linarith
      _ ≤ (0.011537853759 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13210 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13210 13210 0.011 ≤ 0.008316777736 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13210 13210 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13210 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13210 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13210 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13210 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159029749623 + 0.011537853759 + (0.008316777736 : ℝ) *
        (1 + 2 * (0.280105771085 + 0.011537853759) / (0.560525741582 * 114.934764105556))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13210]

end BstLean.Part269.N13210

/-! The original eight local profiles supply actual 13210 moment certificates. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13210 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052283311156 ∧
    0 ≤ bN 13210 BstLean.Part154.csC (groupTheta g) ∧ bN 13210 BstLean.Part154.csC (groupTheta g) ≤ 0.001325277651 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13210 13210 0.011
      (momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13210 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13210 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13210 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228655442000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13210 0.011
      (momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13210 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13210
/-! The actual computed-centre upper energy formula at 13210. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13210

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13210)
open BstLean.Part268 (cell13210)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084126933338
  | 2 => 0.085048924772
  | 3 => 0.085966159712
  | 4 => 0.086879373032
  | 5 => 0.087789472531
  | 6 => 0.088697566895
  | 7 => 0.089604996723
  | 8 => 0.090513368751
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13210 13210 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13210 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13210

/-! Actual upper energy certificates on all 43 source endpoints at 13210. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13210)
open BstLean.Part268 (cell13210)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13210 (gMinus 13210) (1 - (cell13210 i).lower) ≤ 1 ∧
    energyUpper 13210 (gMinus 13210) (BstLean.Part211.gPlus 13210)
      (finiteEnergy 13210 13210 0.011) (1 - (cell13210 i).lower) ≤
      (cell13210 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨10,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨11,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨12,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨13,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨14,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨15,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨16,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨17,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨18,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨19,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨20,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨21,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨22,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨23,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨24,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨25,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨26,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨27,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨28,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨29,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨30,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨31,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨32,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨33,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨34,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨35,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨36,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨37,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨38,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨39,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨40,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨41,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨42,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨43,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨44,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨45,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨46,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨47,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨48,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨49,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨50,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨51,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13210) (by norm_num)
        (q := 1 - (cell13210 ⟨52,by decide⟩).lower)
        (by norm_num [cell13210]) (by norm_num [cell13210])
      exact ⟨E.1,E.2.trans (by norm_num [cell13210])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13210

/-! Source-cell containment and simple scalar guards at 13210. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13210)
open BstLean.Part268 (cell13210)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13210 ⟨10,by decide⟩).lower ∧ (cell13210 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13210 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13210 ⟨11,by decide⟩).lower ∧ (cell13210 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13210 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13210 ⟨12,by decide⟩).lower ∧ (cell13210 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13210 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13210 ⟨13,by decide⟩).lower ∧ (cell13210 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13210 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13210 ⟨14,by decide⟩).lower ∧ (cell13210 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13210 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13210 ⟨15,by decide⟩).lower ∧ (cell13210 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13210 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13210 ⟨16,by decide⟩).lower ∧ (cell13210 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13210 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13210 ⟨17,by decide⟩).lower ∧ (cell13210 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13210 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13210 ⟨18,by decide⟩).lower ∧ (cell13210 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13210 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13210 ⟨19,by decide⟩).lower ∧ (cell13210 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13210 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13210 ⟨20,by decide⟩).lower ∧ (cell13210 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13210 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13210 ⟨21,by decide⟩).lower ∧ (cell13210 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13210 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13210 ⟨22,by decide⟩).lower ∧ (cell13210 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13210 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13210 ⟨23,by decide⟩).lower ∧ (cell13210 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13210 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13210 ⟨24,by decide⟩).lower ∧ (cell13210 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13210 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13210 ⟨25,by decide⟩).lower ∧ (cell13210 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13210 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13210 ⟨26,by decide⟩).lower ∧ (cell13210 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13210 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13210 ⟨27,by decide⟩).lower ∧ (cell13210 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13210 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13210 ⟨28,by decide⟩).lower ∧ (cell13210 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13210 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13210 ⟨29,by decide⟩).lower ∧ (cell13210 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13210 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13210 ⟨30,by decide⟩).lower ∧ (cell13210 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13210 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13210 ⟨31,by decide⟩).lower ∧ (cell13210 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13210 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13210 ⟨32,by decide⟩).lower ∧ (cell13210 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13210 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13210 ⟨33,by decide⟩).lower ∧ (cell13210 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13210 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13210 ⟨34,by decide⟩).lower ∧ (cell13210 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13210 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13210 ⟨35,by decide⟩).lower ∧ (cell13210 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13210 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13210 ⟨36,by decide⟩).lower ∧ (cell13210 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13210 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13210 ⟨37,by decide⟩).lower ∧ (cell13210 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13210 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13210 ⟨38,by decide⟩).lower ∧ (cell13210 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13210 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13210 ⟨39,by decide⟩).lower ∧ (cell13210 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13210 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13210 ⟨40,by decide⟩).lower ∧ (cell13210 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13210 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13210 ⟨41,by decide⟩).lower ∧ (cell13210 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13210 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13210 ⟨42,by decide⟩).lower ∧ (cell13210 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13210 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13210 ⟨43,by decide⟩).lower ∧ (cell13210 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13210 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13210 ⟨44,by decide⟩).lower ∧ (cell13210 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13210 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13210 ⟨45,by decide⟩).lower ∧ (cell13210 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13210 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13210 ⟨46,by decide⟩).lower ∧ (cell13210 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13210 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13210 ⟨47,by decide⟩).lower ∧ (cell13210 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13210 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13210 ⟨48,by decide⟩).lower ∧ (cell13210 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13210 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13210 ⟨49,by decide⟩).lower ∧ (cell13210 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13210 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13210 ⟨50,by decide⟩).lower ∧ (cell13210 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13210 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13210 ⟨51,by decide⟩).lower ∧ (cell13210 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13210 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13210 ⟨52,by decide⟩).lower ∧ (cell13210 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13210 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13210 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13210 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13210,cell13210,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13210 i).lower ∧
    (cell13210 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13210 i).upper ≤ (0.532 : ℝ) ∧
    (cell13210 i).centre ≤ (0.1 : ℝ) ∧ (cell13210 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13210 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13210 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13210

/-! The local source numeric instances at 13210 have no network premises. -/
namespace BstLean.Part269.N13210
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13210)
open BstLean.Part268 (cell13210)

noncomputable def sourceNumerics13210 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13210 (cell13210 i)
      scalarRow13210.M scalarRow13210.H scalarRow13210.xi := by
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
    energy_allowance := scalarRow13210.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13210]
    centre_nonneg := (scalarRow13210.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13210])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13210
/-! Actual 13211 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13211 ≤ (1.035103811769 : ℝ) := by
  have hr : (114.939114317102 : ℝ) ≤ √(13211 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.939114317102 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13211 13211 (11 / 1000) ≤
    (0.008316462961 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13211) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.939114317102 : ℝ) ≤ √(13211 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13211)
  have hdiv : K / √(13211 : ℝ) ≤ K / 114.939114317102 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.939114317102 ≤ (0.008316462961 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13211.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13211 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13211 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13211 := gPlus_lower 13211
end BstLean.Part269.N13211

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13211
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035103811768 : ℝ) ≤ wn 13211 := by
  have hn : √(13211 : ℝ) ≤ 114.939114317103 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13211 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.939114317103 ≤ 2 / √(13211 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241973244 : ℝ) ≤ rhoBar 13211 BstLean.Part154.csC ∧
    rhoBar 13211 BstLean.Part154.csC ≤ 0.000241973618 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035103811768 : ℝ) / (1.295212 * 13211) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035103811769 : ℝ) / (1.29521 * 13211) := by gcongr
      _ ≤ (0.000241973618 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13211 BstLean.Part154.csC) ≤ 0.000967953024 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13211 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) ≤ 0.000184820744 ∧
    cc1 (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) ≤ 0.000117602736 ∧
    cc2 (rhoBar 13211 BstLean.Part154.csC) ≤ 0.000068269374 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13211 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13211 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13211 BstLean.Part154.csC * nuR (rhoBar 13211 BstLean.Part154.csC)) ≤ 0.000483961874 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241973618 : ℝ) * 0.000967953024 := by gcongr
      _ ≤ (0.000483961874 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13211 BstLean.Part154.csC) * nuR (rhoBar 13211 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967953024 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13211 BstLean.Part154.csC) * rhoBar 13211 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241973618 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241973618 / 2 + 0.399 * 0.000967953024 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184820744 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483961874 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117602736 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241973618 / 1.414213562 := by gcongr
      _ ≤ (0.000068269374 : ℝ) := by norm_num

end BstLean.Part269.N13211

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13211
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) ≤ 1.47515E-7 := by
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13211 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13211 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13211 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184820744 : ℝ) ^ 2 + 0.000117602736 ^ 2 + 3 * 0.000068269374 ^ 2 +
        2 * 0.797885 * 0.000184820744 * 0.000117602736 + 2 * 0.000184820744 * 0.000068269374 +
        4 * 0.797885 * 0.000117602736 * 0.000068269374 := by gcongr
    _ ≤ (1.47515E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13211 BstLean.Part154.csC Θ ≤ 0.002524135914 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13211 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13211 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13211 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035103811769 * 1.47515E-7 / (0.000241973244 : ℝ) := by gcongr
    _ ≤ 0.002524135914 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13211 BstLean.Part154.csC Θ ≤ 0.002798762894 + 0.000637811185 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13211 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13211 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035103811769 : ℝ) * ((2 * Θ * 0.000241973618 +
        (6863 / 10000) * 0.000241973618 * 13211 * 0.000967953024) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002798762894 + 0.000637811185 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13211 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13211 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13211 0.011 Θ ∧ gammaRatio 13211 0.011 Θ ≤ 0.000083184273 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13211 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035103811769 : ℝ) * 0.525 / ((1 - 0.011) * 13211) := by gcongr
      _ ≤ (0.000083184273 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13211 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13211 0.011 Θ) :=
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
    badAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13211 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13211 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13211 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13211 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13211 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13211 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13211 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13211 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13211 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13211 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035103811769 : ℝ) * 13211 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003116333660 + 0.003161947099 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13211

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13211
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13211 BstLean.Part154.csC) (piBar (rhoBar 13211 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13211 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13211 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13211 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13211 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13211 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13211 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13211 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13211 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13211 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13211 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051448361087 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13211) ≤ 0.010390175600 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13211 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035103811769)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010390175600 + 2 * 0.737676 / 13211) := by gcongr
    _ ≤ (0.051448361087 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13211 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13211

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13211
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525783377 : ℝ) ≤ plow 13211 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13211) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282955887)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325171355) : eMP 13211 0.011 xi bn ≤ 0.001141521957 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13211 : ℝ) * (1 - 0.011))) ≤ 0.000564475359 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325171355 / (13211 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564475359 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564475359 : ℝ) + 3.141593 * 0.052282955887 / (13211 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141521957 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282955887)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325171355) : PiBarMP 13211 12 0.011 xi bn ≤ 0.158071100039 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13211 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036402903113 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.305201106511 : ℝ) ≤ √((13211 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.939114317102 : ℝ) ≤ √(13211 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13211) ≤ 0.121215552648 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036402903113 + 0.052282955887 * 1.772454 / (2 * (114.305201106511 : ℝ))) * (1 + 0.001141521957) +
        8 / (13211 * 114.939114317102) + 0.121215552648 := by gcongr
    _ ≤ (0.158071100039 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282955887)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325171355) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280103026220) :
    parallelOracle 13211 0.011 xi bn cd ≤ 0.159023613439 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13211 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13211 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525783377 : ℝ) ≤ plow 13211 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.939114317102 : ℝ) ≤ √(13211 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280103026220 : ℝ) / (2 * 0.560525783377 * 114.939114317102)) * 0.158071100039 +
        0.280103026220 ^ 2 / (2 * 0.560525783377 * 114.939114317102) := by gcongr
    _ ≤ (0.159023613439 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282955887) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325171355)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280103026220) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13211 13211 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525783377 : ℝ) ≤ plow 13211 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.939114317102 : ℝ) ≤ √(13211 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13211 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13211 Θ 1.22 ≤ 0.011537417075 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.939114317102 := by gcongr <;> linarith
      _ ≤ (0.011537417075 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13211 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13211 13211 0.011 ≤ 0.008316462961 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13211 13211 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13211 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13211 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13211 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13211 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159023613439 + 0.011537417075 + (0.008316462961 : ℝ) *
        (1 + 2 * (0.280103026220 + 0.011537417075) / (0.560525783377 * 114.939114317102))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13211]

end BstLean.Part269.N13211

/-! The original eight local profiles supply actual 13211 moment certificates. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13211 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052282955887 ∧
    0 ≤ bN 13211 BstLean.Part154.csC (groupTheta g) ∧ bN 13211 BstLean.Part154.csC (groupTheta g) ≤ 0.001325171355 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13211 13211 0.011
      (momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13211 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13211 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13211 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228654665133 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13211 0.011
      (momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13211 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13211
/-! The actual computed-centre upper energy formula at 13211. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13211

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13211)
open BstLean.Part268 (cell13211)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084124469557
  | 2 => 0.085046431690
  | 3 => 0.085963633341
  | 4 => 0.086876808417
  | 5 => 0.087786863574
  | 6 => 0.088694906143
  | 7 => 0.089602275140
  | 8 => 0.090510575453
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13211 13211 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13211 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13211

/-! Actual upper energy certificates on all 43 source endpoints at 13211. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13211)
open BstLean.Part268 (cell13211)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13211 (gMinus 13211) (1 - (cell13211 i).lower) ≤ 1 ∧
    energyUpper 13211 (gMinus 13211) (BstLean.Part211.gPlus 13211)
      (finiteEnergy 13211 13211 0.011) (1 - (cell13211 i).lower) ≤
      (cell13211 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨10,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨11,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨12,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨13,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨14,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨15,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨16,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨17,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨18,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨19,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨20,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨21,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨22,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨23,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨24,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨25,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨26,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨27,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨28,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨29,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨30,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨31,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨32,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨33,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨34,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨35,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨36,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨37,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨38,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨39,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨40,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨41,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨42,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨43,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨44,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨45,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨46,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨47,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨48,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨49,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨50,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨51,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13211) (by norm_num)
        (q := 1 - (cell13211 ⟨52,by decide⟩).lower)
        (by norm_num [cell13211]) (by norm_num [cell13211])
      exact ⟨E.1,E.2.trans (by norm_num [cell13211])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13211

/-! Source-cell containment and simple scalar guards at 13211. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13211)
open BstLean.Part268 (cell13211)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13211 ⟨10,by decide⟩).lower ∧ (cell13211 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13211 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13211 ⟨11,by decide⟩).lower ∧ (cell13211 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13211 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13211 ⟨12,by decide⟩).lower ∧ (cell13211 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13211 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13211 ⟨13,by decide⟩).lower ∧ (cell13211 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13211 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13211 ⟨14,by decide⟩).lower ∧ (cell13211 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13211 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13211 ⟨15,by decide⟩).lower ∧ (cell13211 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13211 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13211 ⟨16,by decide⟩).lower ∧ (cell13211 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13211 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13211 ⟨17,by decide⟩).lower ∧ (cell13211 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13211 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13211 ⟨18,by decide⟩).lower ∧ (cell13211 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13211 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13211 ⟨19,by decide⟩).lower ∧ (cell13211 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13211 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13211 ⟨20,by decide⟩).lower ∧ (cell13211 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13211 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13211 ⟨21,by decide⟩).lower ∧ (cell13211 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13211 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13211 ⟨22,by decide⟩).lower ∧ (cell13211 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13211 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13211 ⟨23,by decide⟩).lower ∧ (cell13211 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13211 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13211 ⟨24,by decide⟩).lower ∧ (cell13211 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13211 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13211 ⟨25,by decide⟩).lower ∧ (cell13211 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13211 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13211 ⟨26,by decide⟩).lower ∧ (cell13211 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13211 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13211 ⟨27,by decide⟩).lower ∧ (cell13211 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13211 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13211 ⟨28,by decide⟩).lower ∧ (cell13211 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13211 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13211 ⟨29,by decide⟩).lower ∧ (cell13211 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13211 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13211 ⟨30,by decide⟩).lower ∧ (cell13211 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13211 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13211 ⟨31,by decide⟩).lower ∧ (cell13211 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13211 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13211 ⟨32,by decide⟩).lower ∧ (cell13211 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13211 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13211 ⟨33,by decide⟩).lower ∧ (cell13211 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13211 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13211 ⟨34,by decide⟩).lower ∧ (cell13211 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13211 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13211 ⟨35,by decide⟩).lower ∧ (cell13211 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13211 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13211 ⟨36,by decide⟩).lower ∧ (cell13211 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13211 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13211 ⟨37,by decide⟩).lower ∧ (cell13211 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13211 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13211 ⟨38,by decide⟩).lower ∧ (cell13211 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13211 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13211 ⟨39,by decide⟩).lower ∧ (cell13211 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13211 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13211 ⟨40,by decide⟩).lower ∧ (cell13211 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13211 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13211 ⟨41,by decide⟩).lower ∧ (cell13211 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13211 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13211 ⟨42,by decide⟩).lower ∧ (cell13211 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13211 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13211 ⟨43,by decide⟩).lower ∧ (cell13211 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13211 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13211 ⟨44,by decide⟩).lower ∧ (cell13211 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13211 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13211 ⟨45,by decide⟩).lower ∧ (cell13211 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13211 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13211 ⟨46,by decide⟩).lower ∧ (cell13211 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13211 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13211 ⟨47,by decide⟩).lower ∧ (cell13211 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13211 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13211 ⟨48,by decide⟩).lower ∧ (cell13211 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13211 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13211 ⟨49,by decide⟩).lower ∧ (cell13211 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13211 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13211 ⟨50,by decide⟩).lower ∧ (cell13211 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13211 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13211 ⟨51,by decide⟩).lower ∧ (cell13211 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13211 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13211 ⟨52,by decide⟩).lower ∧ (cell13211 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13211 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13211 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13211 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13211,cell13211,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13211 i).lower ∧
    (cell13211 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13211 i).upper ≤ (0.532 : ℝ) ∧
    (cell13211 i).centre ≤ (0.1 : ℝ) ∧ (cell13211 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13211 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13211 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13211

/-! The local source numeric instances at 13211 have no network premises. -/
namespace BstLean.Part269.N13211
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13211)
open BstLean.Part268 (cell13211)

noncomputable def sourceNumerics13211 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13211 (cell13211 i)
      scalarRow13211.M scalarRow13211.H scalarRow13211.xi := by
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
    energy_allowance := scalarRow13211.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13211]
    centre_nonneg := (scalarRow13211.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13211])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13211
/-! Actual 13212 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13212 ≤ (1.035102471803 : ℝ) := by
  have hr : (114.943464364008 : ℝ) ≤ √(13212 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.943464364008 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13212 13212 (11 / 1000) ≤
    (0.008316148221 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13212) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.943464364008 : ℝ) ≤ √(13212 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13212)
  have hdiv : K / √(13212 : ℝ) ≤ K / 114.943464364008 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.943464364008 ≤ (0.008316148221 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13212.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13212 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13212 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13212 := gPlus_lower 13212
end BstLean.Part269.N13212

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13212
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035102471802 : ℝ) ≤ wn 13212 := by
  have hn : √(13212 : ℝ) ≤ 114.943464364009 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13212 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.943464364009 ≤ 2 / √(13212 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241954616 : ℝ) ≤ rhoBar 13212 BstLean.Part154.csC ∧
    rhoBar 13212 BstLean.Part154.csC ≤ 0.000241954990 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035102471802 : ℝ) / (1.295212 * 13212) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035102471803 : ℝ) / (1.29521 * 13212) := by gcongr
      _ ≤ (0.000241954990 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13212 BstLean.Part154.csC) ≤ 0.000967878503 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13212 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) ≤ 0.000184806515 ∧
    cc1 (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) ≤ 0.000117593682 ∧
    cc2 (rhoBar 13212 BstLean.Part154.csC) ≤ 0.000068264118 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13212 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13212 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13212 BstLean.Part154.csC * nuR (rhoBar 13212 BstLean.Part154.csC)) ≤ 0.000483924616 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241954990 : ℝ) * 0.000967878503 := by gcongr
      _ ≤ (0.000483924616 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13212 BstLean.Part154.csC) * nuR (rhoBar 13212 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967878503 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13212 BstLean.Part154.csC) * rhoBar 13212 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241954990 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241954990 / 2 + 0.399 * 0.000967878503 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184806515 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483924616 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117593682 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241954990 / 1.414213562 := by gcongr
      _ ≤ (0.000068264118 : ℝ) := by norm_num

end BstLean.Part269.N13212

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13212
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) ≤ 1.47493E-7 := by
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13212 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13212 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13212 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184806515 : ℝ) ^ 2 + 0.000117593682 ^ 2 + 3 * 0.000068264118 ^ 2 +
        2 * 0.797885 * 0.000184806515 * 0.000117593682 + 2 * 0.000184806515 * 0.000068264118 +
        4 * 0.797885 * 0.000117593682 * 0.000068264118 := by gcongr
    _ ≤ (1.47493E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13212 BstLean.Part154.csC Θ ≤ 0.002523950507 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13212 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13212 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13212 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035102471803 * 1.47493E-7 / (0.000241954616 : ℝ) := by gcongr
    _ ≤ 0.002523950507 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13212 BstLean.Part154.csC Θ ≤ 0.002798540176 + 0.000637761258 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13212 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13212 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035102471803 : ℝ) * ((2 * Θ * 0.000241954990 +
        (6863 / 10000) * 0.000241954990 * 13212 * 0.000967878503) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002798540176 + 0.000637761258 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13212 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13212 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13212 0.011 Θ ∧ gammaRatio 13212 0.011 Θ ≤ 0.000083177869 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13212 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035102471803 : ℝ) * 0.525 / ((1 - 0.011) * 13212) := by gcongr
      _ ≤ (0.000083177869 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13212 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13212 0.011 Θ) :=
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
    badAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13212 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13212 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13212 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13212 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13212 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13212 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13212 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13212 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13212 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13212 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035102471803 : ℝ) * 13212 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003116110942 + 0.003161711765 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13212

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13212
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13212 BstLean.Part154.csC) (piBar (rhoBar 13212 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13212 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13212 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13212 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13212 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13212 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13212 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13212 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13212 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13212 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13212 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051446393315 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13212) ≤ 0.010389782383 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13212 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035102471803)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010389782383 + 2 * 0.737676 / 13212) := by gcongr
    _ ≤ (0.051446393315 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13212 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13212

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13212
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525825166 : ℝ) ≤ plow 13212 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13212) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282609619)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325074017) : eMP 13212 0.011 xi bn ≤ 0.001141436734 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13212 : ℝ) * (1 - 0.011))) ≤ 0.000564433265 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001325074017 / (13212 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564433265 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564433265 : ℝ) + 3.141593 * 0.052282609619 / (13212 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141436734 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282609619)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325074017) : PiBarMP 13212 12 0.011 xi bn ≤ 0.158065152338 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13212 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036401566134 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.309527161999 : ℝ) ≤ √((13212 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.943464364008 : ℝ) ≤ √(13212 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13212) ≤ 0.121210965233 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036401566134 + 0.052282609619 * 1.772454 / (2 * (114.309527161999 : ℝ))) * (1 + 0.001141436734) +
        8 / (13212 * 114.943464364008) + 0.121210965233 := by gcongr
    _ ≤ (0.158065152338 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282609619)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325074017) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280100301262) :
    parallelOracle 13212 0.011 xi bn cd ≤ 0.159017601501 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13212 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13212 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525825166 : ℝ) ≤ plow 13212 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.943464364008 : ℝ) ≤ √(13212 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280100301262 : ℝ) / (2 * 0.560525825166 * 114.943464364008)) * 0.158065152338 +
        0.280100301262 ^ 2 / (2 * 0.560525825166 * 114.943464364008) := by gcongr
    _ ≤ (0.159017601501 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282609619) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001325074017)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280100301262) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13212 13212 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525825166 : ℝ) ≤ plow 13212 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.943464364008 : ℝ) ≤ √(13212 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13212 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13212 Θ 1.22 ≤ 0.011536980440 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.943464364008 := by gcongr <;> linarith
      _ ≤ (0.011536980440 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13212 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13212 13212 0.011 ≤ 0.008316148221 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13212 13212 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13212 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13212 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13212 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13212 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159017601501 + 0.011536980440 + (0.008316148221 : ℝ) *
        (1 + 2 * (0.280100301262 + 0.011536980440) / (0.560525825166 * 114.943464364008))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13212]

end BstLean.Part269.N13212

/-! The original eight local profiles supply actual 13212 moment certificates. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13212 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052282609619 ∧
    0 ≤ bN 13212 BstLean.Part154.csC (groupTheta g) ∧ bN 13212 BstLean.Part154.csC (groupTheta g) ≤ 0.001325074017 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13212 13212 0.011
      (momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13212 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13212 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13212 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228653907947 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13212 0.011
      (momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13212 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13212
/-! The actual computed-centre upper energy formula at 13212. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13212

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13212)
open BstLean.Part268 (cell13212)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084122006444
  | 2 => 0.085043939299
  | 3 => 0.085961107687
  | 4 => 0.086874244554
  | 5 => 0.087784255409
  | 6 => 0.088692246235
  | 7 => 0.089599554461
  | 8 => 0.090507783132
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13212 13212 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13212 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13212

/-! Actual upper energy certificates on all 43 source endpoints at 13212. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13212)
open BstLean.Part268 (cell13212)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13212 (gMinus 13212) (1 - (cell13212 i).lower) ≤ 1 ∧
    energyUpper 13212 (gMinus 13212) (BstLean.Part211.gPlus 13212)
      (finiteEnergy 13212 13212 0.011) (1 - (cell13212 i).lower) ≤
      (cell13212 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨10,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨11,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨12,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨13,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨14,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨15,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨16,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨17,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨18,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨19,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨20,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨21,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨22,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨23,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨24,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨25,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨26,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨27,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨28,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨29,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨30,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨31,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨32,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨33,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨34,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨35,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨36,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨37,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨38,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨39,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨40,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨41,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨42,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨43,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨44,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨45,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨46,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨47,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨48,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨49,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨50,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨51,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13212) (by norm_num)
        (q := 1 - (cell13212 ⟨52,by decide⟩).lower)
        (by norm_num [cell13212]) (by norm_num [cell13212])
      exact ⟨E.1,E.2.trans (by norm_num [cell13212])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13212

/-! Source-cell containment and simple scalar guards at 13212. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13212)
open BstLean.Part268 (cell13212)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13212 ⟨10,by decide⟩).lower ∧ (cell13212 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13212 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13212 ⟨11,by decide⟩).lower ∧ (cell13212 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13212 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13212 ⟨12,by decide⟩).lower ∧ (cell13212 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13212 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13212 ⟨13,by decide⟩).lower ∧ (cell13212 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13212 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13212 ⟨14,by decide⟩).lower ∧ (cell13212 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13212 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13212 ⟨15,by decide⟩).lower ∧ (cell13212 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13212 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13212 ⟨16,by decide⟩).lower ∧ (cell13212 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13212 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13212 ⟨17,by decide⟩).lower ∧ (cell13212 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13212 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13212 ⟨18,by decide⟩).lower ∧ (cell13212 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13212 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13212 ⟨19,by decide⟩).lower ∧ (cell13212 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13212 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13212 ⟨20,by decide⟩).lower ∧ (cell13212 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13212 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13212 ⟨21,by decide⟩).lower ∧ (cell13212 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13212 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13212 ⟨22,by decide⟩).lower ∧ (cell13212 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13212 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13212 ⟨23,by decide⟩).lower ∧ (cell13212 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13212 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13212 ⟨24,by decide⟩).lower ∧ (cell13212 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13212 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13212 ⟨25,by decide⟩).lower ∧ (cell13212 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13212 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13212 ⟨26,by decide⟩).lower ∧ (cell13212 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13212 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13212 ⟨27,by decide⟩).lower ∧ (cell13212 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13212 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13212 ⟨28,by decide⟩).lower ∧ (cell13212 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13212 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13212 ⟨29,by decide⟩).lower ∧ (cell13212 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13212 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13212 ⟨30,by decide⟩).lower ∧ (cell13212 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13212 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13212 ⟨31,by decide⟩).lower ∧ (cell13212 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13212 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13212 ⟨32,by decide⟩).lower ∧ (cell13212 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13212 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13212 ⟨33,by decide⟩).lower ∧ (cell13212 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13212 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13212 ⟨34,by decide⟩).lower ∧ (cell13212 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13212 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13212 ⟨35,by decide⟩).lower ∧ (cell13212 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13212 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13212 ⟨36,by decide⟩).lower ∧ (cell13212 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13212 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13212 ⟨37,by decide⟩).lower ∧ (cell13212 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13212 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13212 ⟨38,by decide⟩).lower ∧ (cell13212 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13212 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13212 ⟨39,by decide⟩).lower ∧ (cell13212 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13212 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13212 ⟨40,by decide⟩).lower ∧ (cell13212 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13212 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13212 ⟨41,by decide⟩).lower ∧ (cell13212 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13212 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13212 ⟨42,by decide⟩).lower ∧ (cell13212 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13212 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13212 ⟨43,by decide⟩).lower ∧ (cell13212 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13212 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13212 ⟨44,by decide⟩).lower ∧ (cell13212 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13212 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13212 ⟨45,by decide⟩).lower ∧ (cell13212 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13212 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13212 ⟨46,by decide⟩).lower ∧ (cell13212 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13212 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13212 ⟨47,by decide⟩).lower ∧ (cell13212 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13212 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13212 ⟨48,by decide⟩).lower ∧ (cell13212 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13212 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13212 ⟨49,by decide⟩).lower ∧ (cell13212 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13212 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13212 ⟨50,by decide⟩).lower ∧ (cell13212 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13212 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13212 ⟨51,by decide⟩).lower ∧ (cell13212 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13212 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13212 ⟨52,by decide⟩).lower ∧ (cell13212 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13212 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13212 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13212 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13212,cell13212,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13212 i).lower ∧
    (cell13212 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13212 i).upper ≤ (0.532 : ℝ) ∧
    (cell13212 i).centre ≤ (0.1 : ℝ) ∧ (cell13212 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13212 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13212 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13212

/-! The local source numeric instances at 13212 have no network premises. -/
namespace BstLean.Part269.N13212
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13212)
open BstLean.Part268 (cell13212)

noncomputable def sourceNumerics13212 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13212 (cell13212 i)
      scalarRow13212.M scalarRow13212.H scalarRow13212.xi := by
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
    energy_allowance := scalarRow13212.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13212]
    centre_nonneg := (scalarRow13212.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13212])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13212