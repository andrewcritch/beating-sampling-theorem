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
import BstLean.Part269Direction26
import BstLean.Part269Shared26
import BstLean.Part269Finite
import BstLean.Part269Rows26
import BstLean.Part269Source
/-! Actual 13013 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13013 ≤ (1.035372177680 : ℝ) := by
  have hr : (114.074537036097 : ℝ) ≤ √(13013 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.074537036097 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13013 13013 (11 / 1000) ≤
    (0.008379494369 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13013) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.074537036097 : ℝ) ≤ √(13013 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13013)
  have hdiv : K / √(13013 : ℝ) ≤ K / 114.074537036097 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.074537036097 ≤ (0.008379494369 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13013.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13013 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13013 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13013 := gPlus_lower 13013
end BstLean.Part269.N13013

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13013
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035372177679 : ℝ) ≤ wn 13013 := by
  have hn : √(13013 : ℝ) ≤ 114.074537036098 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13013 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.074537036098 ≤ 2 / √(13013 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245718690 : ℝ) ≤ rhoBar 13013 BstLean.Part154.csC ∧
    rhoBar 13013 BstLean.Part154.csC ≤ 0.000245719071 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035372177679 : ℝ) / (1.295212 * 13013) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035372177680 : ℝ) / (1.29521 * 13013) := by gcongr
      _ ≤ (0.000245719071 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13013 BstLean.Part154.csC) ≤ 0.000982936662 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13013 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) ≤ 0.000187681670 ∧
    cc1 (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) ≤ 0.000119423137 ∧
    cc2 (rhoBar 13013 BstLean.Part154.csC) ≤ 0.000069326099 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13013 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13013 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13013 BstLean.Part154.csC * nuR (rhoBar 13013 BstLean.Part154.csC)) ≤ 0.000491453237 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245719071 : ℝ) * 0.000982936662 := by gcongr
      _ ≤ (0.000491453237 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13013 BstLean.Part154.csC) * nuR (rhoBar 13013 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982936662 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13013 BstLean.Part154.csC) * rhoBar 13013 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245719071 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245719071 / 2 + 0.399 * 0.000982936662 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187681670 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491453237 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119423137 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245719071 / 1.414213562 := by gcongr
      _ ≤ (0.000069326099 : ℝ) := by norm_num

end BstLean.Part269.N13013

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13013
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) ≤ 1.52118E-7 := by
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13013 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13013 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13013 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187681670 : ℝ) ^ 2 + 0.000119423137 ^ 2 + 3 * 0.000069326099 ^ 2 +
        2 * 0.797885 * 0.000187681670 * 0.000119423137 + 2 * 0.000187681670 * 0.000069326099 +
        4 * 0.797885 * 0.000119423137 * 0.000069326099 := by gcongr
    _ ≤ (1.52118E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13013 BstLean.Part154.csC Θ ≤ 0.002563887101 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13013 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13013 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13013 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035372177680 * 1.52118E-7 / (0.000245718690 : ℝ) := by gcongr
    _ ≤ 0.002563887101 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13013 BstLean.Part154.csC Θ ≤ 0.002843560854 + 0.000647851637 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13013 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13013 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035372177680 : ℝ) * ((2 * Θ * 0.000245719071 +
        (6863 / 10000) * 0.000245719071 * 13013 * 0.000982936662) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002843560854 + 0.000647851637 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13013 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13013 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13013 0.011 Θ ∧ gammaRatio 13013 0.011 Θ ≤ 0.000084471863 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13013 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035372177680 : ℝ) * 0.525 / ((1 - 0.011) * 13013) := by gcongr
      _ ≤ (0.000084471863 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13013 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13013 0.011 Θ) :=
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
    badAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13013 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13013 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13013 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13013 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13013 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13013 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13013 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13013 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13013 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13013 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035372177680 : ℝ) * 13013 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003226270615 + 0.003211738738 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13013

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13013
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13013 BstLean.Part154.csC) (piBar (rhoBar 13013 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13013 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13013 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13013 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13013 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13013 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13013 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13013 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13013 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13013 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13013 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051842469006 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13013) ≤ 0.010468923321 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13013 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035372177680)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010468923321 + 2 * 0.737676 / 13013) := by gcongr
    _ ≤ (0.051842469006 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13013 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13013

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13013
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517382617 : ℝ) ≤ plow 13013 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13013) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419033453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346040729) : eMP 13013 0.011 xi bn ≤ 0.001159224821 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13013 : ℝ) * (1 - 0.011))) ≤ 0.000573214543 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346040729 / (13013 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573214543 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573214543 : ℝ) + 3.141593 * 0.052419033453 / (13013 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159224821 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419033453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346040729) : PiBarMP 13013 12 0.011 xi bn ≤ 0.159280567443 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13013 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036688427726 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.445392149703 : ℝ) ≤ √((13013 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.074537036097 : ℝ) ≤ √(13013 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13013) ≤ 0.122134252085 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036688427726 + 0.052419033453 * 1.772454 / (2 * (113.445392149703 : ℝ))) * (1 + 0.001159224821) +
        8 / (13013 * 114.074537036097) + 0.122134252085 := by gcongr
    _ ≤ (0.159280567443 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419033453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346040729) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280794502090) :
    parallelOracle 13013 0.011 xi bn cd ≤ 0.160246857633 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13013 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13013 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517382617 : ℝ) ≤ plow 13013 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.074537036097 : ℝ) ≤ √(13013 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280794502090 : ℝ) / (2 * 0.560517382617 * 114.074537036097)) * 0.159280567443 +
        0.280794502090 ^ 2 / (2 * 0.560517382617 * 114.074537036097) := by gcongr
    _ ≤ (0.160246857633 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419033453) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346040729)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280794502090) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13013 13013 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517382617 : ℝ) ≤ plow 13013 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.074537036097 : ℝ) ≤ √(13013 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13013 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13013 Θ 1.22 ≤ 0.011624859802 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.074537036097 := by gcongr <;> linarith
      _ ≤ (0.011624859802 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13013 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13013 13013 0.011 ≤ 0.008379494369 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13013 13013 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13013 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13013 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13013 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13013 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160246857633 + 0.011624859802 + (0.008379494369 : ℝ) *
        (1 + 2 * (0.280794502090 + 0.011624859802) / (0.560517382617 * 114.074537036097))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13013]

end BstLean.Part269.N13013

/-! The original eight local profiles supply actual 13013 moment certificates. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13013 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052419033453 ∧
    0 ≤ bN 13013 BstLean.Part154.csC (groupTheta g) ∧ bN 13013 BstLean.Part154.csC (groupTheta g) ≤ 0.001346040729 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13013 13013 0.011
      (momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13013 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13013 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13013 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228952033084 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13013 0.011
      (momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13013 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13013
/-! The actual computed-centre upper energy formula at 13013. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13013

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13013)
open BstLean.Part268 (cell13013)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084626140820
  | 2 => 0.085554367238
  | 3 => 0.086478734888
  | 4 => 0.087400192233
  | 5 => 0.088319900258
  | 6 => 0.089239265749
  | 7 => 0.090159978017
  | 8 => 0.091084049184
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13013 13013 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13013 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13013

/-! Actual upper energy certificates on all 43 source endpoints at 13013. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13013)
open BstLean.Part268 (cell13013)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13013 (gMinus 13013) (1 - (cell13013 i).lower) ≤ 1 ∧
    energyUpper 13013 (gMinus 13013) (BstLean.Part211.gPlus 13013)
      (finiteEnergy 13013 13013 0.011) (1 - (cell13013 i).lower) ≤
      (cell13013 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨10,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨11,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨12,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨13,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨14,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨15,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨16,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨17,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨18,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨19,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨20,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨21,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨22,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨23,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨24,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨25,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨26,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨27,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨28,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨29,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨30,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨31,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨32,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨33,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨34,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨35,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨36,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨37,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨38,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨39,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨40,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨41,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨42,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨43,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨44,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨45,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨46,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨47,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨48,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨49,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨50,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨51,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13013) (by norm_num)
        (q := 1 - (cell13013 ⟨52,by decide⟩).lower)
        (by norm_num [cell13013]) (by norm_num [cell13013])
      exact ⟨E.1,E.2.trans (by norm_num [cell13013])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13013

/-! Source-cell containment and simple scalar guards at 13013. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13013)
open BstLean.Part268 (cell13013)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13013 ⟨10,by decide⟩).lower ∧ (cell13013 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13013 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13013 ⟨11,by decide⟩).lower ∧ (cell13013 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13013 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13013 ⟨12,by decide⟩).lower ∧ (cell13013 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13013 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13013 ⟨13,by decide⟩).lower ∧ (cell13013 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13013 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13013 ⟨14,by decide⟩).lower ∧ (cell13013 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13013 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13013 ⟨15,by decide⟩).lower ∧ (cell13013 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13013 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13013 ⟨16,by decide⟩).lower ∧ (cell13013 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13013 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13013 ⟨17,by decide⟩).lower ∧ (cell13013 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13013 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13013 ⟨18,by decide⟩).lower ∧ (cell13013 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13013 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13013 ⟨19,by decide⟩).lower ∧ (cell13013 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13013 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13013 ⟨20,by decide⟩).lower ∧ (cell13013 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13013 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13013 ⟨21,by decide⟩).lower ∧ (cell13013 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13013 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13013 ⟨22,by decide⟩).lower ∧ (cell13013 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13013 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13013 ⟨23,by decide⟩).lower ∧ (cell13013 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13013 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13013 ⟨24,by decide⟩).lower ∧ (cell13013 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13013 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13013 ⟨25,by decide⟩).lower ∧ (cell13013 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13013 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13013 ⟨26,by decide⟩).lower ∧ (cell13013 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13013 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13013 ⟨27,by decide⟩).lower ∧ (cell13013 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13013 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13013 ⟨28,by decide⟩).lower ∧ (cell13013 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13013 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13013 ⟨29,by decide⟩).lower ∧ (cell13013 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13013 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13013 ⟨30,by decide⟩).lower ∧ (cell13013 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13013 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13013 ⟨31,by decide⟩).lower ∧ (cell13013 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13013 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13013 ⟨32,by decide⟩).lower ∧ (cell13013 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13013 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13013 ⟨33,by decide⟩).lower ∧ (cell13013 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13013 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13013 ⟨34,by decide⟩).lower ∧ (cell13013 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13013 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13013 ⟨35,by decide⟩).lower ∧ (cell13013 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13013 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13013 ⟨36,by decide⟩).lower ∧ (cell13013 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13013 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13013 ⟨37,by decide⟩).lower ∧ (cell13013 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13013 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13013 ⟨38,by decide⟩).lower ∧ (cell13013 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13013 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13013 ⟨39,by decide⟩).lower ∧ (cell13013 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13013 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13013 ⟨40,by decide⟩).lower ∧ (cell13013 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13013 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13013 ⟨41,by decide⟩).lower ∧ (cell13013 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13013 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13013 ⟨42,by decide⟩).lower ∧ (cell13013 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13013 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13013 ⟨43,by decide⟩).lower ∧ (cell13013 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13013 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13013 ⟨44,by decide⟩).lower ∧ (cell13013 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13013 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13013 ⟨45,by decide⟩).lower ∧ (cell13013 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13013 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13013 ⟨46,by decide⟩).lower ∧ (cell13013 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13013 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13013 ⟨47,by decide⟩).lower ∧ (cell13013 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13013 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13013 ⟨48,by decide⟩).lower ∧ (cell13013 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13013 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13013 ⟨49,by decide⟩).lower ∧ (cell13013 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13013 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13013 ⟨50,by decide⟩).lower ∧ (cell13013 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13013 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13013 ⟨51,by decide⟩).lower ∧ (cell13013 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13013 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13013 ⟨52,by decide⟩).lower ∧ (cell13013 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13013 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13013 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13013 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13013,cell13013,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13013 i).lower ∧
    (cell13013 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13013 i).upper ≤ (0.532 : ℝ) ∧
    (cell13013 i).centre ≤ (0.1 : ℝ) ∧ (cell13013 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13013 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13013 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13013

/-! The local source numeric instances at 13013 have no network premises. -/
namespace BstLean.Part269.N13013
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13013)
open BstLean.Part268 (cell13013)

noncomputable def sourceNumerics13013 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13013 (cell13013 i)
      scalarRow13013.M scalarRow13013.H scalarRow13013.xi := by
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
    energy_allowance := scalarRow13013.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13013]
    centre_nonneg := (scalarRow13013.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13013])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13013
/-! Actual 13014 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13014 ≤ (1.035370806840 : ℝ) := by
  have hr : (114.078920050989 : ℝ) ≤ √(13014 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.078920050989 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13014 13014 (11 / 1000) ≤
    (0.008379172419 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13014) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.078920050989 : ℝ) ≤ √(13014 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13014)
  have hdiv : K / √(13014 : ℝ) ≤ K / 114.078920050989 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.078920050989 ≤ (0.008379172419 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13014.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13014 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13014 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13014 := gPlus_lower 13014
end BstLean.Part269.N13014

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13014
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035370806839 : ℝ) ≤ wn 13014 := by
  have hn : √(13014 : ℝ) ≤ 114.078920050990 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13014 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.078920050990 ≤ 2 / √(13014 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245699484 : ℝ) ≤ rhoBar 13014 BstLean.Part154.csC ∧
    rhoBar 13014 BstLean.Part154.csC ≤ 0.000245699864 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035370806839 : ℝ) / (1.295212 * 13014) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035370806840 : ℝ) / (1.29521 * 13014) := by gcongr
      _ ≤ (0.000245699864 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13014 BstLean.Part154.csC) ≤ 0.000982859825 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13014 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) ≤ 0.000187666999 ∧
    cc1 (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) ≤ 0.000119413802 ∧
    cc2 (rhoBar 13014 BstLean.Part154.csC) ≤ 0.000069320680 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13014 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13014 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13014 BstLean.Part154.csC * nuR (rhoBar 13014 BstLean.Part154.csC)) ≤ 0.000491414821 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245699864 : ℝ) * 0.000982859825 := by gcongr
      _ ≤ (0.000491414821 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13014 BstLean.Part154.csC) * nuR (rhoBar 13014 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982859825 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13014 BstLean.Part154.csC) * rhoBar 13014 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245699864 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245699864 / 2 + 0.399 * 0.000982859825 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187666999 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491414821 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119413802 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245699864 / 1.414213562 := by gcongr
      _ ≤ (0.000069320680 : ℝ) := by norm_num

end BstLean.Part269.N13014

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13014
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) ≤ 1.52094E-7 := by
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13014 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13014 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13014 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187666999 : ℝ) ^ 2 + 0.000119413802 ^ 2 + 3 * 0.000069320680 ^ 2 +
        2 * 0.797885 * 0.000187666999 * 0.000119413802 + 2 * 0.000187666999 * 0.000069320680 +
        4 * 0.797885 * 0.000119413802 * 0.000069320680 := by gcongr
    _ ≤ (1.52094E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13014 BstLean.Part154.csC Θ ≤ 0.002563679581 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13014 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13014 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13014 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035370806840 * 1.52094E-7 / (0.000245699484 : ℝ) := by gcongr
    _ ≤ 0.002563679581 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13014 BstLean.Part154.csC Θ ≤ 0.002843331035 + 0.000647800139 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13014 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13014 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035370806840 : ℝ) * ((2 * Θ * 0.000245699864 +
        (6863 / 10000) * 0.000245699864 * 13014 * 0.000982859825) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002843331035 + 0.000647800139 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13014 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13014 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13014 0.011 Θ ∧ gammaRatio 13014 0.011 Θ ≤ 0.000084465260 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13014 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035370806840 : ℝ) * 0.525 / ((1 - 0.011) * 13014) := by gcongr
      _ ≤ (0.000084465260 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13014 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13014 0.011 Θ) :=
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
    badAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13014 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13014 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13014 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13014 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13014 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13014 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13014 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13014 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13014 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13014 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035370806840 : ℝ) * 13014 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003226040796 + 0.003211479720 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13014

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13014
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13014 BstLean.Part154.csC) (piBar (rhoBar 13014 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13014 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13014 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13014 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13014 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13014 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13014 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13014 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13014 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13014 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13014 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051840455834 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13014) ≤ 0.010468521096 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13014 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035370806840)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010468521096 + 2 * 0.737676 / 13014) := by gcongr
    _ ≤ (0.051840455834 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13014 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13014

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13014
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517425687 : ℝ) ≤ plow 13014 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13014) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418667649)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345931781) : eMP 13014 0.011 xi bn ≤ 0.001159133306 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13014 : ℝ) * (1 - 0.011))) ≤ 0.000573169322 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345931781 / (13014 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573169322 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573169322 : ℝ) + 3.141593 * 0.052418667649 / (13014 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159133306 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418667649)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345931781) : PiBarMP 13014 12 0.011 xi bn ≤ 0.159274365783 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13014 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036686942923 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.449750991352 : ℝ) ≤ √((13014 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.078920050989 : ℝ) ≤ √(13014 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13014) ≤ 0.122129559577 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036686942923 + 0.052418667649 * 1.772454 / (2 * (113.449750991352 : ℝ))) * (1 + 0.001159133306) +
        8 / (13014 * 114.078920050989) + 0.122129559577 := by gcongr
    _ ≤ (0.159274365783 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418667649)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345931781) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280791690050) :
    parallelOracle 13014 0.011 xi bn cd ≤ 0.160240589306 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13014 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13014 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517425687 : ℝ) ≤ plow 13014 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.078920050989 : ℝ) ≤ √(13014 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280791690050 : ℝ) / (2 * 0.560517425687 * 114.078920050989)) * 0.159274365783 +
        0.280791690050 ^ 2 / (2 * 0.560517425687 * 114.078920050989) := by gcongr
    _ ≤ (0.160240589306 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418667649) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345931781)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280791690050) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13014 13014 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517425687 : ℝ) ≤ plow 13014 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.078920050989 : ℝ) ≤ √(13014 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13014 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13014 Θ 1.22 ≤ 0.011624413165 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.078920050989 := by gcongr <;> linarith
      _ ≤ (0.011624413165 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13014 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13014 13014 0.011 ≤ 0.008379172419 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13014 13014 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13014 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13014 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13014 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13014 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160240589306 + 0.011624413165 + (0.008379172419 : ℝ) *
        (1 + 2 * (0.280791690050 + 0.011624413165) / (0.560517425687 * 114.078920050989))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13014]

end BstLean.Part269.N13014

/-! The original eight local profiles supply actual 13014 moment certificates. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13014 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052418667649 ∧
    0 ≤ bN 13014 BstLean.Part154.csC (groupTheta g) ∧ bN 13014 BstLean.Part154.csC (groupTheta g) ≤ 0.001345931781 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13014 13014 0.011
      (momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13014 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13014 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13014 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228951234216 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13014 0.011
      (momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13014 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13014
/-! The actual computed-centre upper energy formula at 13014. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13014

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13014)
open BstLean.Part268 (cell13014)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084623533040
  | 2 => 0.085551725278
  | 3 => 0.086476053581
  | 4 => 0.087397465198
  | 5 => 0.088317119683
  | 6 => 0.089236422136
  | 7 => 0.090157059902
  | 8 => 0.091081042823
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13014 13014 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13014 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13014

/-! Actual upper energy certificates on all 43 source endpoints at 13014. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13014)
open BstLean.Part268 (cell13014)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13014 (gMinus 13014) (1 - (cell13014 i).lower) ≤ 1 ∧
    energyUpper 13014 (gMinus 13014) (BstLean.Part211.gPlus 13014)
      (finiteEnergy 13014 13014 0.011) (1 - (cell13014 i).lower) ≤
      (cell13014 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨10,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨11,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨12,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨13,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨14,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨15,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨16,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨17,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨18,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨19,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨20,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨21,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨22,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨23,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨24,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨25,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨26,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨27,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨28,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨29,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨30,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨31,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨32,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨33,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨34,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨35,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨36,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨37,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨38,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨39,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨40,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨41,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨42,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨43,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨44,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨45,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨46,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨47,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨48,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨49,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨50,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨51,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13014) (by norm_num)
        (q := 1 - (cell13014 ⟨52,by decide⟩).lower)
        (by norm_num [cell13014]) (by norm_num [cell13014])
      exact ⟨E.1,E.2.trans (by norm_num [cell13014])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13014

/-! Source-cell containment and simple scalar guards at 13014. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13014)
open BstLean.Part268 (cell13014)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13014 ⟨10,by decide⟩).lower ∧ (cell13014 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13014 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13014 ⟨11,by decide⟩).lower ∧ (cell13014 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13014 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13014 ⟨12,by decide⟩).lower ∧ (cell13014 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13014 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13014 ⟨13,by decide⟩).lower ∧ (cell13014 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13014 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13014 ⟨14,by decide⟩).lower ∧ (cell13014 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13014 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13014 ⟨15,by decide⟩).lower ∧ (cell13014 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13014 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13014 ⟨16,by decide⟩).lower ∧ (cell13014 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13014 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13014 ⟨17,by decide⟩).lower ∧ (cell13014 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13014 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13014 ⟨18,by decide⟩).lower ∧ (cell13014 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13014 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13014 ⟨19,by decide⟩).lower ∧ (cell13014 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13014 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13014 ⟨20,by decide⟩).lower ∧ (cell13014 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13014 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13014 ⟨21,by decide⟩).lower ∧ (cell13014 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13014 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13014 ⟨22,by decide⟩).lower ∧ (cell13014 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13014 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13014 ⟨23,by decide⟩).lower ∧ (cell13014 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13014 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13014 ⟨24,by decide⟩).lower ∧ (cell13014 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13014 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13014 ⟨25,by decide⟩).lower ∧ (cell13014 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13014 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13014 ⟨26,by decide⟩).lower ∧ (cell13014 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13014 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13014 ⟨27,by decide⟩).lower ∧ (cell13014 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13014 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13014 ⟨28,by decide⟩).lower ∧ (cell13014 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13014 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13014 ⟨29,by decide⟩).lower ∧ (cell13014 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13014 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13014 ⟨30,by decide⟩).lower ∧ (cell13014 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13014 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13014 ⟨31,by decide⟩).lower ∧ (cell13014 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13014 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13014 ⟨32,by decide⟩).lower ∧ (cell13014 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13014 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13014 ⟨33,by decide⟩).lower ∧ (cell13014 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13014 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13014 ⟨34,by decide⟩).lower ∧ (cell13014 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13014 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13014 ⟨35,by decide⟩).lower ∧ (cell13014 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13014 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13014 ⟨36,by decide⟩).lower ∧ (cell13014 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13014 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13014 ⟨37,by decide⟩).lower ∧ (cell13014 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13014 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13014 ⟨38,by decide⟩).lower ∧ (cell13014 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13014 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13014 ⟨39,by decide⟩).lower ∧ (cell13014 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13014 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13014 ⟨40,by decide⟩).lower ∧ (cell13014 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13014 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13014 ⟨41,by decide⟩).lower ∧ (cell13014 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13014 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13014 ⟨42,by decide⟩).lower ∧ (cell13014 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13014 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13014 ⟨43,by decide⟩).lower ∧ (cell13014 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13014 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13014 ⟨44,by decide⟩).lower ∧ (cell13014 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13014 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13014 ⟨45,by decide⟩).lower ∧ (cell13014 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13014 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13014 ⟨46,by decide⟩).lower ∧ (cell13014 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13014 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13014 ⟨47,by decide⟩).lower ∧ (cell13014 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13014 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13014 ⟨48,by decide⟩).lower ∧ (cell13014 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13014 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13014 ⟨49,by decide⟩).lower ∧ (cell13014 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13014 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13014 ⟨50,by decide⟩).lower ∧ (cell13014 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13014 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13014 ⟨51,by decide⟩).lower ∧ (cell13014 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13014 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13014 ⟨52,by decide⟩).lower ∧ (cell13014 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13014 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13014 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13014 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13014,cell13014,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13014 i).lower ∧
    (cell13014 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13014 i).upper ≤ (0.532 : ℝ) ∧
    (cell13014 i).centre ≤ (0.1 : ℝ) ∧ (cell13014 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13014 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13014 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13014

/-! The local source numeric instances at 13014 have no network premises. -/
namespace BstLean.Part269.N13014
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13014)
open BstLean.Part268 (cell13014)

noncomputable def sourceNumerics13014 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13014 (cell13014 i)
      scalarRow13014.M scalarRow13014.H scalarRow13014.xi := by
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
    energy_allowance := scalarRow13014.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13014]
    centre_nonneg := (scalarRow13014.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13014])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13014
/-! Actual 13015 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13015 ≤ (1.035369436158 : ℝ) := by
  have hr : (114.083302897488 : ℝ) ≤ √(13015 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.083302897488 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13015 13015 (11 / 1000) ≤
    (0.008378850506 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13015) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.083302897488 : ℝ) ≤ √(13015 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13015)
  have hdiv : K / √(13015 : ℝ) ≤ K / 114.083302897488 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.083302897488 ≤ (0.008378850506 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13015.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13015 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13015 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13015 := gPlus_lower 13015
end BstLean.Part269.N13015

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13015
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035369436157 : ℝ) ≤ wn 13015 := by
  have hn : √(13015 : ℝ) ≤ 114.083302897489 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13015 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.083302897489 ≤ 2 / √(13015 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245680280 : ℝ) ≤ rhoBar 13015 BstLean.Part154.csC ∧
    rhoBar 13015 BstLean.Part154.csC ≤ 0.000245680661 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035369436157 : ℝ) / (1.295212 * 13015) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035369436158 : ℝ) / (1.29521 * 13015) := by gcongr
      _ ≤ (0.000245680661 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13015 BstLean.Part154.csC) ≤ 0.000982783003 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13015 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) ≤ 0.000187652331 ∧
    cc1 (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) ≤ 0.000119404469 ∧
    cc2 (rhoBar 13015 BstLean.Part154.csC) ≤ 0.000069315263 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13015 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13015 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13015 BstLean.Part154.csC * nuR (rhoBar 13015 BstLean.Part154.csC)) ≤ 0.000491376412 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245680661 : ℝ) * 0.000982783003 := by gcongr
      _ ≤ (0.000491376412 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13015 BstLean.Part154.csC) * nuR (rhoBar 13015 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982783003 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13015 BstLean.Part154.csC) * rhoBar 13015 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245680661 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245680661 / 2 + 0.399 * 0.000982783003 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187652331 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491376412 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119404469 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245680661 / 1.414213562 := by gcongr
      _ ≤ (0.000069315263 : ℝ) := by norm_num

end BstLean.Part269.N13015

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13015
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) ≤ 1.52070E-7 := by
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13015 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13015 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13015 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187652331 : ℝ) ^ 2 + 0.000119404469 ^ 2 + 3 * 0.000069315263 ^ 2 +
        2 * 0.797885 * 0.000187652331 * 0.000119404469 + 2 * 0.000187652331 * 0.000069315263 +
        4 * 0.797885 * 0.000119404469 * 0.000069315263 := by gcongr
    _ ≤ (1.52070E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13015 BstLean.Part154.csC Θ ≤ 0.002563472008 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13015 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13015 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13015 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035369436158 * 1.52070E-7 / (0.000245680280 : ℝ) := by gcongr
    _ ≤ 0.002563472008 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13015 BstLean.Part154.csC Θ ≤ 0.002843101272 + 0.000647748651 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13015 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13015 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035369436158 : ℝ) * ((2 * Θ * 0.000245680661 +
        (6863 / 10000) * 0.000245680661 * 13015 * 0.000982783003) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002843101272 + 0.000647748651 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13015 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13015 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13015 0.011 Θ ∧ gammaRatio 13015 0.011 Θ ≤ 0.000084458658 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13015 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035369436158 : ℝ) * 0.525 / ((1 - 0.011) * 13015) := by gcongr
      _ ≤ (0.000084458658 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13015 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13015 0.011 Θ) :=
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
    badAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13015 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13015 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13015 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13015 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13015 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13015 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13015 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13015 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13015 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13015 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035369436158 : ℝ) * 13015 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003225811033 + 0.003211220659 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13015

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13015
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13015 BstLean.Part154.csC) (piBar (rhoBar 13015 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13015 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13015 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13015 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13015 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13015 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13015 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13015 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13015 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13015 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13015 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051838442890 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13015) ≤ 0.010468118916 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13015 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035369436158)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010468118916 + 2 * 0.737676 / 13015) := by gcongr
    _ ≤ (0.051838442890 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13015 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13015

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13015
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517468751 : ℝ) ≤ plow 13015 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13015) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418301879)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345822805) : eMP 13015 0.011 xi bn ≤ 0.001159041788 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13015 : ℝ) * (1 - 0.011))) ≤ 0.000573124099 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345822805 / (13015 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573124099 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573124099 : ℝ) + 3.141593 * 0.052418301879 / (13015 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159041788 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418301879)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345822805) : PiBarMP 13015 12 0.011 xi bn ≤ 0.159268164223 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13015 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036685457678 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.454109665538 : ℝ) ≤ √((13015 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.083302897488 : ℝ) ≤ √(13015 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13015) ≤ 0.122124867609 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036685457678 + 0.052418301879 * 1.772454 / (2 * (113.454109665538 : ℝ))) * (1 + 0.001159041788) +
        8 / (13015 * 114.083302897488) + 0.122124867609 := by gcongr
    _ ≤ (0.159268164223 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418301879)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345822805) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280788878310) :
    parallelOracle 13015 0.011 xi bn cd ≤ 0.160234321088 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13015 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13015 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517468751 : ℝ) ≤ plow 13015 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.083302897488 : ℝ) ≤ √(13015 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280788878310 : ℝ) / (2 * 0.560517468751 * 114.083302897488)) * 0.159268164223 +
        0.280788878310 ^ 2 / (2 * 0.560517468751 * 114.083302897488) := by gcongr
    _ ≤ (0.160234321088 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052418301879) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345822805)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280788878310) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13015 13015 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517468751 : ℝ) ≤ plow 13015 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.083302897488 : ℝ) ≤ √(13015 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13015 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13015 Θ 1.22 ≤ 0.011623966579 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.083302897488 := by gcongr <;> linarith
      _ ≤ (0.011623966579 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13015 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13015 13015 0.011 ≤ 0.008378850506 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13015 13015 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13015 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13015 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13015 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13015 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160234321088 + 0.011623966579 + (0.008378850506 : ℝ) *
        (1 + 2 * (0.280788878310 + 0.011623966579) / (0.560517468751 * 114.083302897488))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13015]

end BstLean.Part269.N13015

/-! The original eight local profiles supply actual 13015 moment certificates. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13015 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052418301879 ∧
    0 ≤ bN 13015 BstLean.Part154.csC (groupTheta g) ∧ bN 13015 BstLean.Part154.csC (groupTheta g) ≤ 0.001345822805 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13015 13015 0.011
      (momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13015 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13015 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13015 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228950435420 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13015 0.011
      (momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13015 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13015
/-! The actual computed-centre upper energy formula at 13015. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13015

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13015)
open BstLean.Part268 (cell13015)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084620926057
  | 2 => 0.085549084143
  | 3 => 0.086473373133
  | 4 => 0.087394739066
  | 5 => 0.088314340063
  | 6 => 0.089233579542
  | 7 => 0.090154142885
  | 8 => 0.091078037655
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13015 13015 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13015 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13015

/-! Actual upper energy certificates on all 43 source endpoints at 13015. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13015)
open BstLean.Part268 (cell13015)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13015 (gMinus 13015) (1 - (cell13015 i).lower) ≤ 1 ∧
    energyUpper 13015 (gMinus 13015) (BstLean.Part211.gPlus 13015)
      (finiteEnergy 13015 13015 0.011) (1 - (cell13015 i).lower) ≤
      (cell13015 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨10,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨11,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨12,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨13,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨14,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨15,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨16,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨17,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨18,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨19,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨20,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨21,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨22,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨23,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨24,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨25,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨26,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨27,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨28,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨29,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨30,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨31,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨32,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨33,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨34,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨35,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨36,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨37,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨38,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨39,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨40,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨41,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨42,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨43,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨44,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨45,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨46,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨47,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨48,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨49,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨50,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨51,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13015) (by norm_num)
        (q := 1 - (cell13015 ⟨52,by decide⟩).lower)
        (by norm_num [cell13015]) (by norm_num [cell13015])
      exact ⟨E.1,E.2.trans (by norm_num [cell13015])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13015

/-! Source-cell containment and simple scalar guards at 13015. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13015)
open BstLean.Part268 (cell13015)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13015 ⟨10,by decide⟩).lower ∧ (cell13015 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13015 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13015 ⟨11,by decide⟩).lower ∧ (cell13015 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13015 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13015 ⟨12,by decide⟩).lower ∧ (cell13015 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13015 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13015 ⟨13,by decide⟩).lower ∧ (cell13015 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13015 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13015 ⟨14,by decide⟩).lower ∧ (cell13015 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13015 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13015 ⟨15,by decide⟩).lower ∧ (cell13015 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13015 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13015 ⟨16,by decide⟩).lower ∧ (cell13015 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13015 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13015 ⟨17,by decide⟩).lower ∧ (cell13015 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13015 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13015 ⟨18,by decide⟩).lower ∧ (cell13015 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13015 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13015 ⟨19,by decide⟩).lower ∧ (cell13015 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13015 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13015 ⟨20,by decide⟩).lower ∧ (cell13015 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13015 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13015 ⟨21,by decide⟩).lower ∧ (cell13015 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13015 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13015 ⟨22,by decide⟩).lower ∧ (cell13015 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13015 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13015 ⟨23,by decide⟩).lower ∧ (cell13015 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13015 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13015 ⟨24,by decide⟩).lower ∧ (cell13015 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13015 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13015 ⟨25,by decide⟩).lower ∧ (cell13015 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13015 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13015 ⟨26,by decide⟩).lower ∧ (cell13015 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13015 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13015 ⟨27,by decide⟩).lower ∧ (cell13015 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13015 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13015 ⟨28,by decide⟩).lower ∧ (cell13015 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13015 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13015 ⟨29,by decide⟩).lower ∧ (cell13015 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13015 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13015 ⟨30,by decide⟩).lower ∧ (cell13015 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13015 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13015 ⟨31,by decide⟩).lower ∧ (cell13015 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13015 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13015 ⟨32,by decide⟩).lower ∧ (cell13015 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13015 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13015 ⟨33,by decide⟩).lower ∧ (cell13015 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13015 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13015 ⟨34,by decide⟩).lower ∧ (cell13015 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13015 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13015 ⟨35,by decide⟩).lower ∧ (cell13015 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13015 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13015 ⟨36,by decide⟩).lower ∧ (cell13015 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13015 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13015 ⟨37,by decide⟩).lower ∧ (cell13015 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13015 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13015 ⟨38,by decide⟩).lower ∧ (cell13015 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13015 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13015 ⟨39,by decide⟩).lower ∧ (cell13015 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13015 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13015 ⟨40,by decide⟩).lower ∧ (cell13015 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13015 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13015 ⟨41,by decide⟩).lower ∧ (cell13015 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13015 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13015 ⟨42,by decide⟩).lower ∧ (cell13015 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13015 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13015 ⟨43,by decide⟩).lower ∧ (cell13015 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13015 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13015 ⟨44,by decide⟩).lower ∧ (cell13015 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13015 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13015 ⟨45,by decide⟩).lower ∧ (cell13015 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13015 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13015 ⟨46,by decide⟩).lower ∧ (cell13015 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13015 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13015 ⟨47,by decide⟩).lower ∧ (cell13015 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13015 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13015 ⟨48,by decide⟩).lower ∧ (cell13015 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13015 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13015 ⟨49,by decide⟩).lower ∧ (cell13015 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13015 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13015 ⟨50,by decide⟩).lower ∧ (cell13015 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13015 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13015 ⟨51,by decide⟩).lower ∧ (cell13015 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13015 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13015 ⟨52,by decide⟩).lower ∧ (cell13015 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13015 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13015 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13015 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13015,cell13015,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13015 i).lower ∧
    (cell13015 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13015 i).upper ≤ (0.532 : ℝ) ∧
    (cell13015 i).centre ≤ (0.1 : ℝ) ∧ (cell13015 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13015 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13015 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13015

/-! The local source numeric instances at 13015 have no network premises. -/
namespace BstLean.Part269.N13015
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13015)
open BstLean.Part268 (cell13015)

noncomputable def sourceNumerics13015 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13015 (cell13015 i)
      scalarRow13015.M scalarRow13015.H scalarRow13015.xi := by
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
    energy_allowance := scalarRow13015.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13015]
    centre_nonneg := (scalarRow13015.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13015])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13015
/-! Actual 13016 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13016 ≤ (1.035368065635 : ℝ) := by
  have hr : (114.087685575613 : ℝ) ≤ √(13016 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.087685575613 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13016 13016 (11 / 1000) ≤
    (0.008378528630 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13016) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.087685575613 : ℝ) ≤ √(13016 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13016)
  have hdiv : K / √(13016 : ℝ) ≤ K / 114.087685575613 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.087685575613 ≤ (0.008378528630 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13016.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13016 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13016 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13016 := gPlus_lower 13016
end BstLean.Part269.N13016

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13016
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035368065634 : ℝ) ≤ wn 13016 := by
  have hn : √(13016 : ℝ) ≤ 114.087685575614 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13016 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.087685575614 ≤ 2 / √(13016 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245661080 : ℝ) ≤ rhoBar 13016 BstLean.Part154.csC ∧
    rhoBar 13016 BstLean.Part154.csC ≤ 0.000245661460 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035368065634 : ℝ) / (1.295212 * 13016) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035368065635 : ℝ) / (1.29521 * 13016) := by gcongr
      _ ≤ (0.000245661460 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13016 BstLean.Part154.csC) ≤ 0.000982706190 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13016 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) ≤ 0.000187637665 ∧
    cc1 (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) ≤ 0.000119395136 ∧
    cc2 (rhoBar 13016 BstLean.Part154.csC) ≤ 0.000069309845 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13016 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13016 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13016 BstLean.Part154.csC * nuR (rhoBar 13016 BstLean.Part154.csC)) ≤ 0.000491338008 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245661460 : ℝ) * 0.000982706190 := by gcongr
      _ ≤ (0.000491338008 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13016 BstLean.Part154.csC) * nuR (rhoBar 13016 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982706190 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13016 BstLean.Part154.csC) * rhoBar 13016 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245661460 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245661460 / 2 + 0.399 * 0.000982706190 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187637665 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491338008 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119395136 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245661460 / 1.414213562 := by gcongr
      _ ≤ (0.000069309845 : ℝ) := by norm_num

end BstLean.Part269.N13016

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13016
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) ≤ 1.52046E-7 := by
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13016 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13016 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13016 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187637665 : ℝ) ^ 2 + 0.000119395136 ^ 2 + 3 * 0.000069309845 ^ 2 +
        2 * 0.797885 * 0.000187637665 * 0.000119395136 + 2 * 0.000187637665 * 0.000069309845 +
        4 * 0.797885 * 0.000119395136 * 0.000069309845 := by gcongr
    _ ≤ (1.52046E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13016 BstLean.Part154.csC Θ ≤ 0.002563264363 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13016 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13016 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13016 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035368065635 * 1.52046E-7 / (0.000245661080 : ℝ) := by gcongr
    _ ≤ 0.002563264363 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13016 BstLean.Part154.csC Θ ≤ 0.002842871527 + 0.000647697170 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13016 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13016 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035368065635 : ℝ) * ((2 * Θ * 0.000245661460 +
        (6863 / 10000) * 0.000245661460 * 13016 * 0.000982706190) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002842871527 + 0.000647697170 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13016 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13016 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13016 0.011 Θ ∧ gammaRatio 13016 0.011 Θ ≤ 0.000084452058 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13016 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035368065635 : ℝ) * 0.525 / ((1 - 0.011) * 13016) := by gcongr
      _ ≤ (0.000084452058 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13016 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13016 0.011 Θ) :=
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
    badAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13016 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13016 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13016 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13016 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13016 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13016 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13016 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13016 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13016 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13016 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035368065635 : ℝ) * 13016 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003225581288 + 0.003210961533 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13016

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13016
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13016 BstLean.Part154.csC) (piBar (rhoBar 13016 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13016 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13016 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13016 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13016 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13016 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13016 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13016 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13016 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13016 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13016 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051836430188 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13016) ≤ 0.010467716784 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13016 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035368065635)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010467716784 + 2 * 0.737676 / 13016) := by gcongr
    _ ≤ (0.051836430188 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13016 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13016

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13016
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517511808 : ℝ) ≤ plow 13016 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13016) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417936093)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345713791) : eMP 13016 0.011 xi bn ≤ 0.001158950260 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13016 : ℝ) * (1 - 0.011))) ≤ 0.000573078871 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345713791 / (13016 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573078871 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573078871 : ℝ) + 3.141593 * 0.052417936093 / (13016 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158950260 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417936093)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345713791) : PiBarMP 13016 12 0.011 xi bn ≤ 0.159261962628 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13016 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036683971855 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.458468172278 : ℝ) ≤ √((13016 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.087685575613 : ℝ) ≤ √(13016 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13016) ≤ 0.122120176183 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036683971855 + 0.052417936093 * 1.772454 / (2 * (113.458468172278 : ℝ))) * (1 + 0.001158950260) +
        8 / (13016 * 114.087685575613) + 0.122120176183 := by gcongr
    _ ≤ (0.159261962628 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417936093)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345713791) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280786066775) :
    parallelOracle 13016 0.011 xi bn cd ≤ 0.160228052842 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13016 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13016 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517511808 : ℝ) ≤ plow 13016 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.087685575613 : ℝ) ≤ √(13016 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280786066775 : ℝ) / (2 * 0.560517511808 * 114.087685575613)) * 0.159261962628 +
        0.280786066775 ^ 2 / (2 * 0.560517511808 * 114.087685575613) := by gcongr
    _ ≤ (0.160228052842 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417936093) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345713791)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280786066775) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13016 13016 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517511808 : ℝ) ≤ plow 13016 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.087685575613 : ℝ) ≤ √(13016 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13016 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13016 Θ 1.22 ≤ 0.011623520044 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.087685575613 := by gcongr <;> linarith
      _ ≤ (0.011623520044 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13016 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13016 13016 0.011 ≤ 0.008378528630 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13016 13016 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13016 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13016 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13016 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13016 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160228052842 + 0.011623520044 + (0.008378528630 : ℝ) *
        (1 + 2 * (0.280786066775 + 0.011623520044) / (0.560517511808 * 114.087685575613))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13016]

end BstLean.Part269.N13016

/-! The original eight local profiles supply actual 13016 moment certificates. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13016 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052417936093 ∧
    0 ≤ bN 13016 BstLean.Part154.csC (groupTheta g) ∧ bN 13016 BstLean.Part154.csC (groupTheta g) ≤ 0.001345713791 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13016 13016 0.011
      (momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13016 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13016 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13016 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228949636587 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13016 0.011
      (momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13016 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13016
/-! The actual computed-centre upper energy formula at 13016. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13016

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13016)
open BstLean.Part268 (cell13016)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084618319870
  | 2 => 0.085546443833
  | 3 => 0.086470693545
  | 4 => 0.087392013836
  | 5 => 0.088311561397
  | 6 => 0.089230737967
  | 7 => 0.090151226965
  | 8 => 0.091075033677
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13016 13016 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13016 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13016

/-! Actual upper energy certificates on all 43 source endpoints at 13016. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13016)
open BstLean.Part268 (cell13016)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13016 (gMinus 13016) (1 - (cell13016 i).lower) ≤ 1 ∧
    energyUpper 13016 (gMinus 13016) (BstLean.Part211.gPlus 13016)
      (finiteEnergy 13016 13016 0.011) (1 - (cell13016 i).lower) ≤
      (cell13016 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨10,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨11,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨12,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨13,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨14,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨15,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨16,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨17,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨18,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨19,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨20,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨21,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨22,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨23,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨24,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨25,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨26,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨27,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨28,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨29,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨30,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨31,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨32,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨33,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨34,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨35,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨36,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨37,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨38,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨39,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨40,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨41,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨42,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨43,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨44,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨45,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨46,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨47,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨48,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨49,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨50,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨51,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13016) (by norm_num)
        (q := 1 - (cell13016 ⟨52,by decide⟩).lower)
        (by norm_num [cell13016]) (by norm_num [cell13016])
      exact ⟨E.1,E.2.trans (by norm_num [cell13016])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13016

/-! Source-cell containment and simple scalar guards at 13016. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13016)
open BstLean.Part268 (cell13016)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13016 ⟨10,by decide⟩).lower ∧ (cell13016 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13016 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13016 ⟨11,by decide⟩).lower ∧ (cell13016 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13016 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13016 ⟨12,by decide⟩).lower ∧ (cell13016 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13016 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13016 ⟨13,by decide⟩).lower ∧ (cell13016 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13016 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13016 ⟨14,by decide⟩).lower ∧ (cell13016 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13016 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13016 ⟨15,by decide⟩).lower ∧ (cell13016 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13016 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13016 ⟨16,by decide⟩).lower ∧ (cell13016 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13016 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13016 ⟨17,by decide⟩).lower ∧ (cell13016 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13016 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13016 ⟨18,by decide⟩).lower ∧ (cell13016 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13016 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13016 ⟨19,by decide⟩).lower ∧ (cell13016 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13016 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13016 ⟨20,by decide⟩).lower ∧ (cell13016 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13016 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13016 ⟨21,by decide⟩).lower ∧ (cell13016 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13016 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13016 ⟨22,by decide⟩).lower ∧ (cell13016 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13016 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13016 ⟨23,by decide⟩).lower ∧ (cell13016 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13016 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13016 ⟨24,by decide⟩).lower ∧ (cell13016 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13016 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13016 ⟨25,by decide⟩).lower ∧ (cell13016 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13016 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13016 ⟨26,by decide⟩).lower ∧ (cell13016 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13016 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13016 ⟨27,by decide⟩).lower ∧ (cell13016 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13016 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13016 ⟨28,by decide⟩).lower ∧ (cell13016 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13016 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13016 ⟨29,by decide⟩).lower ∧ (cell13016 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13016 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13016 ⟨30,by decide⟩).lower ∧ (cell13016 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13016 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13016 ⟨31,by decide⟩).lower ∧ (cell13016 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13016 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13016 ⟨32,by decide⟩).lower ∧ (cell13016 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13016 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13016 ⟨33,by decide⟩).lower ∧ (cell13016 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13016 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13016 ⟨34,by decide⟩).lower ∧ (cell13016 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13016 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13016 ⟨35,by decide⟩).lower ∧ (cell13016 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13016 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13016 ⟨36,by decide⟩).lower ∧ (cell13016 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13016 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13016 ⟨37,by decide⟩).lower ∧ (cell13016 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13016 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13016 ⟨38,by decide⟩).lower ∧ (cell13016 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13016 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13016 ⟨39,by decide⟩).lower ∧ (cell13016 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13016 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13016 ⟨40,by decide⟩).lower ∧ (cell13016 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13016 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13016 ⟨41,by decide⟩).lower ∧ (cell13016 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13016 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13016 ⟨42,by decide⟩).lower ∧ (cell13016 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13016 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13016 ⟨43,by decide⟩).lower ∧ (cell13016 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13016 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13016 ⟨44,by decide⟩).lower ∧ (cell13016 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13016 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13016 ⟨45,by decide⟩).lower ∧ (cell13016 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13016 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13016 ⟨46,by decide⟩).lower ∧ (cell13016 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13016 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13016 ⟨47,by decide⟩).lower ∧ (cell13016 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13016 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13016 ⟨48,by decide⟩).lower ∧ (cell13016 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13016 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13016 ⟨49,by decide⟩).lower ∧ (cell13016 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13016 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13016 ⟨50,by decide⟩).lower ∧ (cell13016 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13016 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13016 ⟨51,by decide⟩).lower ∧ (cell13016 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13016 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13016 ⟨52,by decide⟩).lower ∧ (cell13016 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13016 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13016 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13016 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13016,cell13016,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13016 i).lower ∧
    (cell13016 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13016 i).upper ≤ (0.532 : ℝ) ∧
    (cell13016 i).centre ≤ (0.1 : ℝ) ∧ (cell13016 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13016 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13016 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13016

/-! The local source numeric instances at 13016 have no network premises. -/
namespace BstLean.Part269.N13016
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13016)
open BstLean.Part268 (cell13016)

noncomputable def sourceNumerics13016 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13016 (cell13016 i)
      scalarRow13016.M scalarRow13016.H scalarRow13016.xi := by
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
    energy_allowance := scalarRow13016.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13016]
    centre_nonneg := (scalarRow13016.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13016])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13016
/-! Actual 13017 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13017 ≤ (1.035366695271 : ℝ) := by
  have hr : (114.092068085384 : ℝ) ≤ √(13017 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.092068085384 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13017 13017 (11 / 1000) ≤
    (0.008378206791 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13017) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.092068085384 : ℝ) ≤ √(13017 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13017)
  have hdiv : K / √(13017 : ℝ) ≤ K / 114.092068085384 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.092068085384 ≤ (0.008378206791 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13017.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13017 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13017 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13017 := gPlus_lower 13017
end BstLean.Part269.N13017

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13017
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035366695270 : ℝ) ≤ wn 13017 := by
  have hn : √(13017 : ℝ) ≤ 114.092068085385 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13017 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.092068085385 ≤ 2 / √(13017 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245641883 : ℝ) ≤ rhoBar 13017 BstLean.Part154.csC ∧
    rhoBar 13017 BstLean.Part154.csC ≤ 0.000245642263 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035366695270 : ℝ) / (1.295212 * 13017) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035366695271 : ℝ) / (1.29521 * 13017) := by gcongr
      _ ≤ (0.000245642263 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13017 BstLean.Part154.csC) ≤ 0.000982629393 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13017 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) ≤ 0.000187623001 ∧
    cc1 (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) ≤ 0.000119385806 ∧
    cc2 (rhoBar 13017 BstLean.Part154.csC) ≤ 0.000069304429 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13017 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13017 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13017 BstLean.Part154.csC * nuR (rhoBar 13017 BstLean.Part154.csC)) ≤ 0.000491299612 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245642263 : ℝ) * 0.000982629393 := by gcongr
      _ ≤ (0.000491299612 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13017 BstLean.Part154.csC) * nuR (rhoBar 13017 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982629393 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13017 BstLean.Part154.csC) * rhoBar 13017 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245642263 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245642263 / 2 + 0.399 * 0.000982629393 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187623001 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491299612 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119385806 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245642263 / 1.414213562 := by gcongr
      _ ≤ (0.000069304429 : ℝ) := by norm_num

end BstLean.Part269.N13017

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13017
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) ≤ 1.52023E-7 := by
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13017 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13017 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13017 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187623001 : ℝ) ^ 2 + 0.000119385806 ^ 2 + 3 * 0.000069304429 ^ 2 +
        2 * 0.797885 * 0.000187623001 * 0.000119385806 + 2 * 0.000187623001 * 0.000069304429 +
        4 * 0.797885 * 0.000119385806 * 0.000069304429 := by gcongr
    _ ≤ (1.52023E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13017 BstLean.Part154.csC Θ ≤ 0.002563073515 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13017 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13017 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13017 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035366695271 * 1.52023E-7 / (0.000245641883 : ℝ) := by gcongr
    _ ≤ 0.002563073515 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13017 BstLean.Part154.csC Θ ≤ 0.002842641842 + 0.000647645699 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13017 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13017 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035366695271 : ℝ) * ((2 * Θ * 0.000245642263 +
        (6863 / 10000) * 0.000245642263 * 13017 * 0.000982629393) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002842641842 + 0.000647645699 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13017 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13017 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13017 0.011 Θ ∧ gammaRatio 13017 0.011 Θ ≤ 0.000084445458 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13017 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035366695271 : ℝ) * 0.525 / ((1 - 0.011) * 13017) := by gcongr
      _ ≤ (0.000084445458 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13017 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13017 0.011 Θ) :=
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
    badAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13017 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13017 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13017 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13017 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13017 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13017 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13017 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13017 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13017 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13017 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035366695271 : ℝ) * 13017 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003225351603 + 0.003210719214 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13017

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13017
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13017 BstLean.Part154.csC) (piBar (rhoBar 13017 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13017 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13017 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13017 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13017 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13017 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13017 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13017 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13017 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13017 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13017 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051834417713 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13017) ≤ 0.010467314697 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13017 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035366695271)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010467314697 + 2 * 0.737676 / 13017) := by gcongr
    _ ≤ (0.051834417713 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13017 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13017

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13017
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517554859 : ℝ) ≤ plow 13017 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13017) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417579191)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345613596) : eMP 13017 0.011 xi bn ≤ 0.001158862496 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13017 : ℝ) * (1 - 0.011))) ≤ 0.000573035524 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345613596 / (13017 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573035524 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573035524 : ℝ) + 3.141593 * 0.052417579191 / (13017 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158862496 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417579191)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345613596) : PiBarMP 13017 12 0.011 xi bn ≤ 0.159255882069 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13017 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036682606178 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.462826511593 : ℝ) ≤ √((13017 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.092068085384 : ℝ) ≤ √(13017 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13017) ≤ 0.122115485297 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036682606178 + 0.052417579191 * 1.772454 / (2 * (113.462826511593 : ℝ))) * (1 + 0.001158862496) +
        8 / (13017 * 114.092068085384) + 0.122115485297 := by gcongr
    _ ≤ (0.159255882069 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417579191)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345613596) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280783274865) :
    parallelOracle 13017 0.011 xi bn cd ≤ 0.160221906016 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13017 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13017 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517554859 : ℝ) ≤ plow 13017 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.092068085384 : ℝ) ≤ √(13017 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280783274865 : ℝ) / (2 * 0.560517554859 * 114.092068085384)) * 0.159255882069 +
        0.280783274865 ^ 2 / (2 * 0.560517554859 * 114.092068085384) := by gcongr
    _ ≤ (0.160221906016 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417579191) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345613596)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280783274865) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13017 13017 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517554859 : ℝ) ≤ plow 13017 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.092068085384 : ℝ) ≤ √(13017 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13017 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13017 Θ 1.22 ≤ 0.011623073561 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.092068085384 := by gcongr <;> linarith
      _ ≤ (0.011623073561 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13017 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13017 13017 0.011 ≤ 0.008378206791 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13017 13017 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13017 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13017 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13017 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13017 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160221906016 + 0.011623073561 + (0.008378206791 : ℝ) *
        (1 + 2 * (0.280783274865 + 0.011623073561) / (0.560517554859 * 114.092068085384))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13017]

end BstLean.Part269.N13017

/-! The original eight local profiles supply actual 13017 moment certificates. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13017 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052417579191 ∧
    0 ≤ bN 13017 BstLean.Part154.csC (groupTheta g) ∧ bN 13017 BstLean.Part154.csC (groupTheta g) ≤ 0.001345613596 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13017 13017 0.011
      (momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13017 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13017 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13017 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228948857152 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13017 0.011
      (momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13017 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13017
/-! The actual computed-centre upper energy formula at 13017. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13017

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13017)
open BstLean.Part268 (cell13017)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084615714480
  | 2 => 0.085543804346
  | 3 => 0.086468014814
  | 4 => 0.087389289507
  | 5 => 0.088308783686
  | 6 => 0.089227897410
  | 7 => 0.090148312141
  | 8 => 0.091072030890
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13017 13017 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13017 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13017

/-! Actual upper energy certificates on all 43 source endpoints at 13017. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13017)
open BstLean.Part268 (cell13017)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13017 (gMinus 13017) (1 - (cell13017 i).lower) ≤ 1 ∧
    energyUpper 13017 (gMinus 13017) (BstLean.Part211.gPlus 13017)
      (finiteEnergy 13017 13017 0.011) (1 - (cell13017 i).lower) ≤
      (cell13017 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨10,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨11,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨12,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨13,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨14,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨15,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨16,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨17,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨18,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨19,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨20,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨21,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨22,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨23,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨24,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨25,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨26,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨27,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨28,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨29,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨30,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨31,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨32,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨33,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨34,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨35,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨36,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨37,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨38,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨39,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨40,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨41,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨42,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨43,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨44,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨45,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨46,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨47,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨48,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨49,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨50,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨51,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13017) (by norm_num)
        (q := 1 - (cell13017 ⟨52,by decide⟩).lower)
        (by norm_num [cell13017]) (by norm_num [cell13017])
      exact ⟨E.1,E.2.trans (by norm_num [cell13017])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13017

/-! Source-cell containment and simple scalar guards at 13017. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13017)
open BstLean.Part268 (cell13017)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13017 ⟨10,by decide⟩).lower ∧ (cell13017 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13017 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13017 ⟨11,by decide⟩).lower ∧ (cell13017 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13017 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13017 ⟨12,by decide⟩).lower ∧ (cell13017 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13017 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13017 ⟨13,by decide⟩).lower ∧ (cell13017 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13017 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13017 ⟨14,by decide⟩).lower ∧ (cell13017 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13017 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13017 ⟨15,by decide⟩).lower ∧ (cell13017 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13017 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13017 ⟨16,by decide⟩).lower ∧ (cell13017 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13017 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13017 ⟨17,by decide⟩).lower ∧ (cell13017 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13017 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13017 ⟨18,by decide⟩).lower ∧ (cell13017 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13017 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13017 ⟨19,by decide⟩).lower ∧ (cell13017 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13017 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13017 ⟨20,by decide⟩).lower ∧ (cell13017 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13017 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13017 ⟨21,by decide⟩).lower ∧ (cell13017 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13017 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13017 ⟨22,by decide⟩).lower ∧ (cell13017 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13017 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13017 ⟨23,by decide⟩).lower ∧ (cell13017 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13017 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13017 ⟨24,by decide⟩).lower ∧ (cell13017 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13017 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13017 ⟨25,by decide⟩).lower ∧ (cell13017 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13017 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13017 ⟨26,by decide⟩).lower ∧ (cell13017 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13017 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13017 ⟨27,by decide⟩).lower ∧ (cell13017 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13017 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13017 ⟨28,by decide⟩).lower ∧ (cell13017 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13017 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13017 ⟨29,by decide⟩).lower ∧ (cell13017 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13017 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13017 ⟨30,by decide⟩).lower ∧ (cell13017 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13017 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13017 ⟨31,by decide⟩).lower ∧ (cell13017 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13017 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13017 ⟨32,by decide⟩).lower ∧ (cell13017 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13017 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13017 ⟨33,by decide⟩).lower ∧ (cell13017 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13017 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13017 ⟨34,by decide⟩).lower ∧ (cell13017 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13017 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13017 ⟨35,by decide⟩).lower ∧ (cell13017 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13017 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13017 ⟨36,by decide⟩).lower ∧ (cell13017 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13017 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13017 ⟨37,by decide⟩).lower ∧ (cell13017 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13017 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13017 ⟨38,by decide⟩).lower ∧ (cell13017 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13017 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13017 ⟨39,by decide⟩).lower ∧ (cell13017 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13017 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13017 ⟨40,by decide⟩).lower ∧ (cell13017 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13017 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13017 ⟨41,by decide⟩).lower ∧ (cell13017 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13017 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13017 ⟨42,by decide⟩).lower ∧ (cell13017 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13017 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13017 ⟨43,by decide⟩).lower ∧ (cell13017 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13017 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13017 ⟨44,by decide⟩).lower ∧ (cell13017 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13017 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13017 ⟨45,by decide⟩).lower ∧ (cell13017 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13017 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13017 ⟨46,by decide⟩).lower ∧ (cell13017 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13017 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13017 ⟨47,by decide⟩).lower ∧ (cell13017 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13017 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13017 ⟨48,by decide⟩).lower ∧ (cell13017 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13017 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13017 ⟨49,by decide⟩).lower ∧ (cell13017 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13017 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13017 ⟨50,by decide⟩).lower ∧ (cell13017 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13017 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13017 ⟨51,by decide⟩).lower ∧ (cell13017 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13017 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13017 ⟨52,by decide⟩).lower ∧ (cell13017 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13017 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13017 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13017 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13017,cell13017,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13017 i).lower ∧
    (cell13017 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13017 i).upper ≤ (0.532 : ℝ) ∧
    (cell13017 i).centre ≤ (0.1 : ℝ) ∧ (cell13017 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13017 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13017 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13017

/-! The local source numeric instances at 13017 have no network premises. -/
namespace BstLean.Part269.N13017
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13017)
open BstLean.Part268 (cell13017)

noncomputable def sourceNumerics13017 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13017 (cell13017 i)
      scalarRow13017.M scalarRow13017.H scalarRow13017.xi := by
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
    energy_allowance := scalarRow13017.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13017]
    centre_nonneg := (scalarRow13017.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13017])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13017
/-! Actual 13018 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13018 ≤ (1.035365325066 : ℝ) := by
  have hr : (114.096450426820 : ℝ) ≤ √(13018 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.096450426820 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13018 13018 (11 / 1000) ≤
    (0.008377884989 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13018) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.096450426820 : ℝ) ≤ √(13018 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13018)
  have hdiv : K / √(13018 : ℝ) ≤ K / 114.096450426820 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.096450426820 ≤ (0.008377884989 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13018.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13018 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13018 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13018 := gPlus_lower 13018
end BstLean.Part269.N13018

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13018
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035365325065 : ℝ) ≤ wn 13018 := by
  have hn : √(13018 : ℝ) ≤ 114.096450426821 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13018 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.096450426821 ≤ 2 / √(13018 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245622688 : ℝ) ≤ rhoBar 13018 BstLean.Part154.csC ∧
    rhoBar 13018 BstLean.Part154.csC ≤ 0.000245623068 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035365325065 : ℝ) / (1.295212 * 13018) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035365325066 : ℝ) / (1.29521 * 13018) := by gcongr
      _ ≤ (0.000245623068 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13018 BstLean.Part154.csC) ≤ 0.000982552603 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13018 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) ≤ 0.000187608339 ∧
    cc1 (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) ≤ 0.000119376477 ∧
    cc2 (rhoBar 13018 BstLean.Part154.csC) ≤ 0.000069299014 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13018 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13018 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13018 BstLean.Part154.csC * nuR (rhoBar 13018 BstLean.Part154.csC)) ≤ 0.000491261219 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245623068 : ℝ) * 0.000982552603 := by gcongr
      _ ≤ (0.000491261219 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13018 BstLean.Part154.csC) * nuR (rhoBar 13018 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982552603 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13018 BstLean.Part154.csC) * rhoBar 13018 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245623068 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245623068 / 2 + 0.399 * 0.000982552603 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187608339 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491261219 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119376477 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245623068 / 1.414213562 := by gcongr
      _ ≤ (0.000069299014 : ℝ) := by norm_num

end BstLean.Part269.N13018

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13018
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) ≤ 1.51999E-7 := by
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13018 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13018 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13018 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187608339 : ℝ) ^ 2 + 0.000119376477 ^ 2 + 3 * 0.000069299014 ^ 2 +
        2 * 0.797885 * 0.000187608339 * 0.000119376477 + 2 * 0.000187608339 * 0.000069299014 +
        4 * 0.797885 * 0.000119376477 * 0.000069299014 := by gcongr
    _ ≤ (1.51999E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13018 BstLean.Part154.csC Θ ≤ 0.002562865757 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13018 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13018 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13018 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035365325066 * 1.51999E-7 / (0.000245622688 : ℝ) := by gcongr
    _ ≤ 0.002562865757 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13018 BstLean.Part154.csC Θ ≤ 0.002842412167 + 0.000647594233 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13018 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13018 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035365325066 : ℝ) * ((2 * Θ * 0.000245623068 +
        (6863 / 10000) * 0.000245623068 * 13018 * 0.000982552603) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002842412167 + 0.000647594233 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13018 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13018 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13018 0.011 Θ ∧ gammaRatio 13018 0.011 Θ ≤ 0.000084438860 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13018 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035365325066 : ℝ) * 0.525 / ((1 - 0.011) * 13018) := by gcongr
      _ ≤ (0.000084438860 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13018 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13018 0.011 Θ) :=
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
    badAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13018 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13018 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13018 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13018 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13018 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13018 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13018 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13018 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13018 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13018 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035365325066 : ℝ) * 13018 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003225121928 + 0.003210459990 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13018

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13018
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13018 BstLean.Part154.csC) (piBar (rhoBar 13018 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13018 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13018 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13018 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13018 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13018 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13018 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13018 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13018 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13018 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13018 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051832405474 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13018) ≤ 0.010466912657 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13018 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035365325066)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010466912657 + 2 * 0.737676 / 13018) := by gcongr
    _ ≤ (0.051832405474 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13018 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13018

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13018
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517597902 : ℝ) ≤ plow 13018 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13018) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417213423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345504523) : eMP 13018 0.011 xi bn ≤ 0.001158770956 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13018 : ℝ) * (1 - 0.011))) ≤ 0.000572990290 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345504523 / (13018 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572990290 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572990290 : ℝ) + 3.141593 * 0.052417213423 / (13018 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158770956 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417213423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345504523) : PiBarMP 13018 12 0.011 xi bn ≤ 0.159249680639 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13018 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036681119435 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.467184683502 : ℝ) ≤ √((13018 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.096450426820 : ℝ) ≤ √(13018 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13018) ≤ 0.122110794952 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036681119435 + 0.052417213423 * 1.772454 / (2 * (113.467184683502 : ℝ))) * (1 + 0.001158770956) +
        8 / (13018 * 114.096450426820) + 0.122110794952 := by gcongr
    _ ≤ (0.159249680639 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417213423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345504523) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280780463826) :
    parallelOracle 13018 0.011 xi bn cd ≤ 0.160215637952 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13018 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13018 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517597902 : ℝ) ≤ plow 13018 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.096450426820 : ℝ) ≤ √(13018 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280780463826 : ℝ) / (2 * 0.560517597902 * 114.096450426820)) * 0.159249680639 +
        0.280780463826 ^ 2 / (2 * 0.560517597902 * 114.096450426820) := by gcongr
    _ ≤ (0.160215637952 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052417213423) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345504523)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280780463826) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13018 13018 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517597902 : ℝ) ≤ plow 13018 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.096450426820 : ℝ) ≤ √(13018 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13018 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13018 Θ 1.22 ≤ 0.011622627129 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.096450426820 := by gcongr <;> linarith
      _ ≤ (0.011622627129 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13018 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13018 13018 0.011 ≤ 0.008377884989 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13018 13018 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13018 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13018 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13018 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13018 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160215637952 + 0.011622627129 + (0.008377884989 : ℝ) *
        (1 + 2 * (0.280780463826 + 0.011622627129) / (0.560517597902 * 114.096450426820))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13018]

end BstLean.Part269.N13018

/-! The original eight local profiles supply actual 13018 moment certificates. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13018 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052417213423 ∧
    0 ≤ bN 13018 BstLean.Part154.csC (groupTheta g) ∧ bN 13018 BstLean.Part154.csC (groupTheta g) ≤ 0.001345504523 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13018 13018 0.011
      (momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13018 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13018 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13018 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228948058352 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13018 0.011
      (momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13018 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13018
/-! The actual computed-centre upper energy formula at 13018. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13018

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13018)
open BstLean.Part268 (cell13018)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084613109884
  | 2 => 0.085541165682
  | 3 => 0.086465336942
  | 4 => 0.087386566078
  | 5 => 0.088306006927
  | 6 => 0.089225057871
  | 7 => 0.090145398411
  | 8 => 0.091069029292
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13018 13018 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13018 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13018

/-! Actual upper energy certificates on all 43 source endpoints at 13018. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13018)
open BstLean.Part268 (cell13018)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13018 (gMinus 13018) (1 - (cell13018 i).lower) ≤ 1 ∧
    energyUpper 13018 (gMinus 13018) (BstLean.Part211.gPlus 13018)
      (finiteEnergy 13018 13018 0.011) (1 - (cell13018 i).lower) ≤
      (cell13018 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨10,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨11,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨12,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨13,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨14,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨15,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨16,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨17,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨18,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨19,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨20,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨21,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨22,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨23,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨24,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨25,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨26,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨27,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨28,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨29,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨30,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨31,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨32,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨33,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨34,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨35,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨36,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨37,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨38,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨39,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨40,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨41,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨42,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨43,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨44,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨45,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨46,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨47,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨48,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨49,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨50,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨51,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13018) (by norm_num)
        (q := 1 - (cell13018 ⟨52,by decide⟩).lower)
        (by norm_num [cell13018]) (by norm_num [cell13018])
      exact ⟨E.1,E.2.trans (by norm_num [cell13018])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13018

/-! Source-cell containment and simple scalar guards at 13018. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13018)
open BstLean.Part268 (cell13018)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13018 ⟨10,by decide⟩).lower ∧ (cell13018 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13018 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13018 ⟨11,by decide⟩).lower ∧ (cell13018 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13018 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13018 ⟨12,by decide⟩).lower ∧ (cell13018 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13018 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13018 ⟨13,by decide⟩).lower ∧ (cell13018 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13018 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13018 ⟨14,by decide⟩).lower ∧ (cell13018 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13018 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13018 ⟨15,by decide⟩).lower ∧ (cell13018 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13018 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13018 ⟨16,by decide⟩).lower ∧ (cell13018 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13018 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13018 ⟨17,by decide⟩).lower ∧ (cell13018 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13018 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13018 ⟨18,by decide⟩).lower ∧ (cell13018 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13018 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13018 ⟨19,by decide⟩).lower ∧ (cell13018 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13018 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13018 ⟨20,by decide⟩).lower ∧ (cell13018 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13018 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13018 ⟨21,by decide⟩).lower ∧ (cell13018 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13018 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13018 ⟨22,by decide⟩).lower ∧ (cell13018 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13018 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13018 ⟨23,by decide⟩).lower ∧ (cell13018 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13018 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13018 ⟨24,by decide⟩).lower ∧ (cell13018 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13018 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13018 ⟨25,by decide⟩).lower ∧ (cell13018 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13018 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13018 ⟨26,by decide⟩).lower ∧ (cell13018 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13018 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13018 ⟨27,by decide⟩).lower ∧ (cell13018 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13018 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13018 ⟨28,by decide⟩).lower ∧ (cell13018 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13018 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13018 ⟨29,by decide⟩).lower ∧ (cell13018 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13018 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13018 ⟨30,by decide⟩).lower ∧ (cell13018 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13018 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13018 ⟨31,by decide⟩).lower ∧ (cell13018 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13018 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13018 ⟨32,by decide⟩).lower ∧ (cell13018 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13018 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13018 ⟨33,by decide⟩).lower ∧ (cell13018 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13018 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13018 ⟨34,by decide⟩).lower ∧ (cell13018 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13018 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13018 ⟨35,by decide⟩).lower ∧ (cell13018 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13018 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13018 ⟨36,by decide⟩).lower ∧ (cell13018 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13018 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13018 ⟨37,by decide⟩).lower ∧ (cell13018 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13018 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13018 ⟨38,by decide⟩).lower ∧ (cell13018 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13018 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13018 ⟨39,by decide⟩).lower ∧ (cell13018 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13018 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13018 ⟨40,by decide⟩).lower ∧ (cell13018 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13018 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13018 ⟨41,by decide⟩).lower ∧ (cell13018 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13018 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13018 ⟨42,by decide⟩).lower ∧ (cell13018 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13018 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13018 ⟨43,by decide⟩).lower ∧ (cell13018 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13018 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13018 ⟨44,by decide⟩).lower ∧ (cell13018 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13018 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13018 ⟨45,by decide⟩).lower ∧ (cell13018 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13018 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13018 ⟨46,by decide⟩).lower ∧ (cell13018 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13018 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13018 ⟨47,by decide⟩).lower ∧ (cell13018 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13018 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13018 ⟨48,by decide⟩).lower ∧ (cell13018 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13018 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13018 ⟨49,by decide⟩).lower ∧ (cell13018 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13018 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13018 ⟨50,by decide⟩).lower ∧ (cell13018 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13018 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13018 ⟨51,by decide⟩).lower ∧ (cell13018 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13018 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13018 ⟨52,by decide⟩).lower ∧ (cell13018 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13018 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13018 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13018 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13018,cell13018,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13018 i).lower ∧
    (cell13018 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13018 i).upper ≤ (0.532 : ℝ) ∧
    (cell13018 i).centre ≤ (0.1 : ℝ) ∧ (cell13018 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13018 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13018 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13018

/-! The local source numeric instances at 13018 have no network premises. -/
namespace BstLean.Part269.N13018
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13018)
open BstLean.Part268 (cell13018)

noncomputable def sourceNumerics13018 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13018 (cell13018 i)
      scalarRow13018.M scalarRow13018.H scalarRow13018.xi := by
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
    energy_allowance := scalarRow13018.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13018]
    centre_nonneg := (scalarRow13018.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13018])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13018
/-! Actual 13019 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13019 ≤ (1.035363955020 : ℝ) := by
  have hr : (114.100832599942 : ℝ) ≤ √(13019 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.100832599942 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13019 13019 (11 / 1000) ≤
    (0.008377563225 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13019) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.100832599942 : ℝ) ≤ √(13019 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13019)
  have hdiv : K / √(13019 : ℝ) ≤ K / 114.100832599942 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.100832599942 ≤ (0.008377563225 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13019.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13019 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13019 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13019 := gPlus_lower 13019
end BstLean.Part269.N13019

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13019
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035363955019 : ℝ) ≤ wn 13019 := by
  have hn : √(13019 : ℝ) ≤ 114.100832599943 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13019 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.100832599943 ≤ 2 / √(13019 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245603497 : ℝ) ≤ rhoBar 13019 BstLean.Part154.csC ∧
    rhoBar 13019 BstLean.Part154.csC ≤ 0.000245603877 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035363955019 : ℝ) / (1.295212 * 13019) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035363955020 : ℝ) / (1.29521 * 13019) := by gcongr
      _ ≤ (0.000245603877 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13019 BstLean.Part154.csC) ≤ 0.000982475830 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13019 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) ≤ 0.000187593681 ∧
    cc1 (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) ≤ 0.000119367149 ∧
    cc2 (rhoBar 13019 BstLean.Part154.csC) ≤ 0.000069293599 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13019 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13019 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13019 BstLean.Part154.csC * nuR (rhoBar 13019 BstLean.Part154.csC)) ≤ 0.000491222835 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245603877 : ℝ) * 0.000982475830 := by gcongr
      _ ≤ (0.000491222835 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13019 BstLean.Part154.csC) * nuR (rhoBar 13019 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982475830 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13019 BstLean.Part154.csC) * rhoBar 13019 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245603877 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245603877 / 2 + 0.399 * 0.000982475830 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187593681 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491222835 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119367149 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245603877 / 1.414213562 := by gcongr
      _ ≤ (0.000069293599 : ℝ) := by norm_num

end BstLean.Part269.N13019

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13019
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) ≤ 1.51975E-7 := by
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13019 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13019 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13019 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187593681 : ℝ) ^ 2 + 0.000119367149 ^ 2 + 3 * 0.000069293599 ^ 2 +
        2 * 0.797885 * 0.000187593681 * 0.000119367149 + 2 * 0.000187593681 * 0.000069293599 +
        4 * 0.797885 * 0.000119367149 * 0.000069293599 := by gcongr
    _ ≤ (1.51975E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13019 BstLean.Part154.csC Θ ≤ 0.002562657927 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13019 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13019 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13019 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035363955020 * 1.51975E-7 / (0.000245603497 : ℝ) := by gcongr
    _ ≤ 0.002562657927 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13019 BstLean.Part154.csC Θ ≤ 0.002842182556 + 0.000647542779 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13019 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13019 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035363955020 : ℝ) * ((2 * Θ * 0.000245603877 +
        (6863 / 10000) * 0.000245603877 * 13019 * 0.000982475830) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002842182556 + 0.000647542779 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13019 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13019 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13019 0.011 Θ ∧ gammaRatio 13019 0.011 Θ ≤ 0.000084432262 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13019 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035363955020 : ℝ) * 0.525 / ((1 - 0.011) * 13019) := by gcongr
      _ ≤ (0.000084432262 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13019 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13019 0.011 Θ) :=
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
    badAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13019 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13019 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13019 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13019 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13019 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13019 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13019 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13019 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13019 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13019 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035363955020 : ℝ) * 13019 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003224892317 + 0.003210200706 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13019

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13019
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13019 BstLean.Part154.csC) (piBar (rhoBar 13019 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13019 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13019 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13019 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13019 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13019 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13019 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13019 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13019 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13019 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13019 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051830393467 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13019) ≤ 0.010466510663 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13019 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035363955020)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010466510663 + 2 * 0.737676 / 13019) := by gcongr
    _ ≤ (0.051830393467 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13019 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13019

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13019
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517640940 : ℝ) ≤ plow 13019 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13019) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416847688)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345395412) : eMP 13019 0.011 xi bn ≤ 0.001158679406 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13019 : ℝ) * (1 - 0.011))) ≤ 0.000572945051 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345395412 / (13019 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572945051 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572945051 : ℝ) + 3.141593 * 0.052416847688 / (13019 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158679406 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416847688)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345395412) : PiBarMP 13019 12 0.011 xi bn ≤ 0.159243479172 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13019 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036679632114 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.471542688023 : ℝ) ≤ √((13019 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.100832599942 : ℝ) ≤ √(13019 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13019) ≤ 0.122106105147 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036679632114 + 0.052416847688 * 1.772454 / (2 * (113.471542688023 : ℝ))) * (1 + 0.001158679406) +
        8 / (13019 * 114.100832599942) + 0.122106105147 := by gcongr
    _ ≤ (0.159243479172 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416847688)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345395412) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280777653089) :
    parallelOracle 13019 0.011 xi bn cd ≤ 0.160209369861 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13019 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13019 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517640940 : ℝ) ≤ plow 13019 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.100832599942 : ℝ) ≤ √(13019 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280777653089 : ℝ) / (2 * 0.560517640940 * 114.100832599942)) * 0.159243479172 +
        0.280777653089 ^ 2 / (2 * 0.560517640940 * 114.100832599942) := by gcongr
    _ ≤ (0.160209369861 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416847688) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345395412)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280777653089) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13019 13019 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517640940 : ℝ) ≤ plow 13019 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.100832599942 : ℝ) ≤ √(13019 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13019 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13019 Θ 1.22 ≤ 0.011622180749 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.100832599942 := by gcongr <;> linarith
      _ ≤ (0.011622180749 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13019 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13019 13019 0.011 ≤ 0.008377563225 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13019 13019 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13019 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13019 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13019 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13019 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160209369861 + 0.011622180749 + (0.008377563225 : ℝ) *
        (1 + 2 * (0.280777653089 + 0.011622180749) / (0.560517640940 * 114.100832599942))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13019]

end BstLean.Part269.N13019

/-! The original eight local profiles supply actual 13019 moment certificates. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13019 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052416847688 ∧
    0 ≤ bN 13019 BstLean.Part154.csC (groupTheta g) ∧ bN 13019 BstLean.Part154.csC (groupTheta g) ≤ 0.001345395412 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13019 13019 0.011
      (momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13019 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13019 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13019 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228947259622 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13019 0.011
      (momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13019 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13019
/-! The actual computed-centre upper energy formula at 13019. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13019

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13019)
open BstLean.Part268 (cell13019)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084610506082
  | 2 => 0.085538527841
  | 3 => 0.086462659926
  | 4 => 0.087383843550
  | 5 => 0.088303231121
  | 6 => 0.089222219347
  | 7 => 0.090142485776
  | 8 => 0.091066028881
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13019 13019 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13019 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13019

/-! Actual upper energy certificates on all 43 source endpoints at 13019. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13019)
open BstLean.Part268 (cell13019)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13019 (gMinus 13019) (1 - (cell13019 i).lower) ≤ 1 ∧
    energyUpper 13019 (gMinus 13019) (BstLean.Part211.gPlus 13019)
      (finiteEnergy 13019 13019 0.011) (1 - (cell13019 i).lower) ≤
      (cell13019 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨10,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨11,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨12,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨13,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨14,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨15,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨16,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨17,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨18,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨19,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨20,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨21,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨22,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨23,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨24,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨25,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨26,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨27,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨28,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨29,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨30,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨31,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨32,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨33,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨34,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨35,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨36,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨37,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨38,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨39,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨40,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨41,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨42,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨43,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨44,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨45,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨46,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨47,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨48,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨49,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨50,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨51,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13019) (by norm_num)
        (q := 1 - (cell13019 ⟨52,by decide⟩).lower)
        (by norm_num [cell13019]) (by norm_num [cell13019])
      exact ⟨E.1,E.2.trans (by norm_num [cell13019])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13019

/-! Source-cell containment and simple scalar guards at 13019. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13019)
open BstLean.Part268 (cell13019)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13019 ⟨10,by decide⟩).lower ∧ (cell13019 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13019 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13019 ⟨11,by decide⟩).lower ∧ (cell13019 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13019 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13019 ⟨12,by decide⟩).lower ∧ (cell13019 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13019 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13019 ⟨13,by decide⟩).lower ∧ (cell13019 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13019 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13019 ⟨14,by decide⟩).lower ∧ (cell13019 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13019 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13019 ⟨15,by decide⟩).lower ∧ (cell13019 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13019 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13019 ⟨16,by decide⟩).lower ∧ (cell13019 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13019 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13019 ⟨17,by decide⟩).lower ∧ (cell13019 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13019 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13019 ⟨18,by decide⟩).lower ∧ (cell13019 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13019 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13019 ⟨19,by decide⟩).lower ∧ (cell13019 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13019 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13019 ⟨20,by decide⟩).lower ∧ (cell13019 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13019 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13019 ⟨21,by decide⟩).lower ∧ (cell13019 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13019 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13019 ⟨22,by decide⟩).lower ∧ (cell13019 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13019 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13019 ⟨23,by decide⟩).lower ∧ (cell13019 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13019 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13019 ⟨24,by decide⟩).lower ∧ (cell13019 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13019 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13019 ⟨25,by decide⟩).lower ∧ (cell13019 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13019 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13019 ⟨26,by decide⟩).lower ∧ (cell13019 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13019 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13019 ⟨27,by decide⟩).lower ∧ (cell13019 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13019 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13019 ⟨28,by decide⟩).lower ∧ (cell13019 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13019 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13019 ⟨29,by decide⟩).lower ∧ (cell13019 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13019 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13019 ⟨30,by decide⟩).lower ∧ (cell13019 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13019 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13019 ⟨31,by decide⟩).lower ∧ (cell13019 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13019 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13019 ⟨32,by decide⟩).lower ∧ (cell13019 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13019 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13019 ⟨33,by decide⟩).lower ∧ (cell13019 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13019 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13019 ⟨34,by decide⟩).lower ∧ (cell13019 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13019 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13019 ⟨35,by decide⟩).lower ∧ (cell13019 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13019 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13019 ⟨36,by decide⟩).lower ∧ (cell13019 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13019 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13019 ⟨37,by decide⟩).lower ∧ (cell13019 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13019 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13019 ⟨38,by decide⟩).lower ∧ (cell13019 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13019 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13019 ⟨39,by decide⟩).lower ∧ (cell13019 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13019 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13019 ⟨40,by decide⟩).lower ∧ (cell13019 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13019 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13019 ⟨41,by decide⟩).lower ∧ (cell13019 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13019 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13019 ⟨42,by decide⟩).lower ∧ (cell13019 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13019 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13019 ⟨43,by decide⟩).lower ∧ (cell13019 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13019 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13019 ⟨44,by decide⟩).lower ∧ (cell13019 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13019 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13019 ⟨45,by decide⟩).lower ∧ (cell13019 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13019 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13019 ⟨46,by decide⟩).lower ∧ (cell13019 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13019 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13019 ⟨47,by decide⟩).lower ∧ (cell13019 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13019 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13019 ⟨48,by decide⟩).lower ∧ (cell13019 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13019 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13019 ⟨49,by decide⟩).lower ∧ (cell13019 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13019 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13019 ⟨50,by decide⟩).lower ∧ (cell13019 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13019 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13019 ⟨51,by decide⟩).lower ∧ (cell13019 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13019 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13019 ⟨52,by decide⟩).lower ∧ (cell13019 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13019 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13019 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13019 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13019,cell13019,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13019 i).lower ∧
    (cell13019 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13019 i).upper ≤ (0.532 : ℝ) ∧
    (cell13019 i).centre ≤ (0.1 : ℝ) ∧ (cell13019 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13019 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13019 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13019

/-! The local source numeric instances at 13019 have no network premises. -/
namespace BstLean.Part269.N13019
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13019)
open BstLean.Part268 (cell13019)

noncomputable def sourceNumerics13019 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13019 (cell13019 i)
      scalarRow13019.M scalarRow13019.H scalarRow13019.xi := by
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
    energy_allowance := scalarRow13019.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13019]
    centre_nonneg := (scalarRow13019.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13019])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13019
/-! Actual 13020 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13020 ≤ (1.035362585133 : ℝ) := by
  have hr : (114.105214604767 : ℝ) ≤ √(13020 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.105214604767 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13020 13020 (11 / 1000) ≤
    (0.008377241497 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13020) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.105214604767 : ℝ) ≤ √(13020 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13020)
  have hdiv : K / √(13020 : ℝ) ≤ K / 114.105214604767 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.105214604767 ≤ (0.008377241497 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13020.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13020 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13020 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13020 := gPlus_lower 13020
end BstLean.Part269.N13020

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13020
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035362585132 : ℝ) ≤ wn 13020 := by
  have hn : √(13020 : ℝ) ≤ 114.105214604768 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13020 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.105214604768 ≤ 2 / √(13020 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245584308 : ℝ) ≤ rhoBar 13020 BstLean.Part154.csC ∧
    rhoBar 13020 BstLean.Part154.csC ≤ 0.000245584688 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035362585132 : ℝ) / (1.295212 * 13020) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035362585133 : ℝ) / (1.29521 * 13020) := by gcongr
      _ ≤ (0.000245584688 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13020 BstLean.Part154.csC) ≤ 0.000982399064 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13020 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) ≤ 0.000187579023 ∧
    cc1 (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) ≤ 0.000119357823 ∧
    cc2 (rhoBar 13020 BstLean.Part154.csC) ≤ 0.000069288185 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13020 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13020 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13020 BstLean.Part154.csC * nuR (rhoBar 13020 BstLean.Part154.csC)) ≤ 0.000491184454 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245584688 : ℝ) * 0.000982399064 := by gcongr
      _ ≤ (0.000491184454 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13020 BstLean.Part154.csC) * nuR (rhoBar 13020 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982399064 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13020 BstLean.Part154.csC) * rhoBar 13020 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245584688 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245584688 / 2 + 0.399 * 0.000982399064 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187579023 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491184454 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119357823 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245584688 / 1.414213562 := by gcongr
      _ ≤ (0.000069288185 : ℝ) := by norm_num

end BstLean.Part269.N13020

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13020
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) ≤ 1.51951E-7 := by
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13020 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13020 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13020 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187579023 : ℝ) ^ 2 + 0.000119357823 ^ 2 + 3 * 0.000069288185 ^ 2 +
        2 * 0.797885 * 0.000187579023 * 0.000119357823 + 2 * 0.000187579023 * 0.000069288185 +
        4 * 0.797885 * 0.000119357823 * 0.000069288185 := by gcongr
    _ ≤ (1.51951E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13020 BstLean.Part154.csC Θ ≤ 0.002562450044 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13020 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13020 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13020 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035362585133 * 1.51951E-7 / (0.000245584308 : ℝ) := by gcongr
    _ ≤ 0.002562450044 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13020 BstLean.Part154.csC Θ ≤ 0.002841952955 + 0.000647491330 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13020 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13020 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035362585133 : ℝ) * ((2 * Θ * 0.000245584688 +
        (6863 / 10000) * 0.000245584688 * 13020 * 0.000982399064) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002841952955 + 0.000647491330 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13020 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13020 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13020 0.011 Θ ∧ gammaRatio 13020 0.011 Θ ≤ 0.000084425665 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13020 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035362585133 : ℝ) * 0.525 / ((1 - 0.011) * 13020) := by gcongr
      _ ≤ (0.000084425665 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13020 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13020 0.011 Θ) :=
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
    badAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13020 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13020 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13020 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13020 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13020 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13020 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13020 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13020 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13020 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13020 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035362585133 : ℝ) * 13020 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003224662716 + 0.003209941374 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13020

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13020
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13020 BstLean.Part154.csC) (piBar (rhoBar 13020 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13020 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13020 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13020 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13020 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13020 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13020 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13020 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13020 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13020 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13020 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051828381697 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13020) ≤ 0.010466108716 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13020 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035362585133)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010466108716 + 2 * 0.737676 / 13020) := by gcongr
    _ ≤ (0.051828381697 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13020 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13020

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13020
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517683970 : ℝ) ≤ plow 13020 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13020) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416481938)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345286274) : eMP 13020 0.011 xi bn ≤ 0.001158587853 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13020 : ℝ) * (1 - 0.011))) ≤ 0.000572899810 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345286274 / (13020 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572899810 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572899810 : ℝ) + 3.141593 * 0.052416481938 / (13020 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158587853 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416481938)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345286274) : PiBarMP 13020 12 0.011 xi bn ≤ 0.159237277818 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13020 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036678144365 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.475900525177 : ℝ) ≤ √((13020 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.105214604767 : ℝ) ≤ √(13020 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13020) ≤ 0.122101415882 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036678144365 + 0.052416481938 * 1.772454 / (2 * (113.475900525177 : ℝ))) * (1 + 0.001158587853) +
        8 / (13020 * 114.105214604767) + 0.122101415882 := by gcongr
    _ ≤ (0.159237277818 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416481938)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345286274) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280774842552) :
    parallelOracle 13020 0.011 xi bn cd ≤ 0.160203101890 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13020 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13020 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517683970 : ℝ) ≤ plow 13020 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.105214604767 : ℝ) ≤ √(13020 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280774842552 : ℝ) / (2 * 0.560517683970 * 114.105214604767)) * 0.159237277818 +
        0.280774842552 ^ 2 / (2 * 0.560517683970 * 114.105214604767) := by gcongr
    _ ≤ (0.160203101890 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416481938) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345286274)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280774842552) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13020 13020 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517683970 : ℝ) ≤ plow 13020 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.105214604767 : ℝ) ≤ √(13020 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13020 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13020 Θ 1.22 ≤ 0.011621734420 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.105214604767 := by gcongr <;> linarith
      _ ≤ (0.011621734420 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13020 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13020 13020 0.011 ≤ 0.008377241497 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13020 13020 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13020 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13020 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13020 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13020 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160203101890 + 0.011621734420 + (0.008377241497 : ℝ) *
        (1 + 2 * (0.280774842552 + 0.011621734420) / (0.560517683970 * 114.105214604767))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13020]

end BstLean.Part269.N13020

/-! The original eight local profiles supply actual 13020 moment certificates. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13020 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052416481938 ∧
    0 ≤ bN 13020 BstLean.Part154.csC (groupTheta g) ∧ bN 13020 BstLean.Part154.csC (groupTheta g) ≤ 0.001345286274 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13020 13020 0.011
      (momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13020 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13020 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13020 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228946460855 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13020 0.011
      (momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13020 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13020
/-! The actual computed-centre upper energy formula at 13020. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13020

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13020)
open BstLean.Part268 (cell13020)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084607903074
  | 2 => 0.085535890820
  | 3 => 0.086459983766
  | 4 => 0.087381121919
  | 5 => 0.088300456265
  | 6 => 0.089219381838
  | 7 => 0.090139574233
  | 8 => 0.091063029657
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13020 13020 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13020 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13020

/-! Actual upper energy certificates on all 43 source endpoints at 13020. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13020)
open BstLean.Part268 (cell13020)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13020 (gMinus 13020) (1 - (cell13020 i).lower) ≤ 1 ∧
    energyUpper 13020 (gMinus 13020) (BstLean.Part211.gPlus 13020)
      (finiteEnergy 13020 13020 0.011) (1 - (cell13020 i).lower) ≤
      (cell13020 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨10,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨11,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨12,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨13,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨14,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨15,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨16,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨17,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨18,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨19,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨20,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨21,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨22,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨23,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨24,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨25,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨26,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨27,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨28,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨29,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨30,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨31,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨32,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨33,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨34,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨35,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨36,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨37,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨38,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨39,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨40,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨41,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨42,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨43,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨44,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨45,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨46,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨47,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨48,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨49,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨50,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨51,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13020) (by norm_num)
        (q := 1 - (cell13020 ⟨52,by decide⟩).lower)
        (by norm_num [cell13020]) (by norm_num [cell13020])
      exact ⟨E.1,E.2.trans (by norm_num [cell13020])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13020

/-! Source-cell containment and simple scalar guards at 13020. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13020)
open BstLean.Part268 (cell13020)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13020 ⟨10,by decide⟩).lower ∧ (cell13020 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13020 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13020 ⟨11,by decide⟩).lower ∧ (cell13020 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13020 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13020 ⟨12,by decide⟩).lower ∧ (cell13020 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13020 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13020 ⟨13,by decide⟩).lower ∧ (cell13020 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13020 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13020 ⟨14,by decide⟩).lower ∧ (cell13020 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13020 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13020 ⟨15,by decide⟩).lower ∧ (cell13020 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13020 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13020 ⟨16,by decide⟩).lower ∧ (cell13020 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13020 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13020 ⟨17,by decide⟩).lower ∧ (cell13020 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13020 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13020 ⟨18,by decide⟩).lower ∧ (cell13020 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13020 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13020 ⟨19,by decide⟩).lower ∧ (cell13020 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13020 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13020 ⟨20,by decide⟩).lower ∧ (cell13020 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13020 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13020 ⟨21,by decide⟩).lower ∧ (cell13020 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13020 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13020 ⟨22,by decide⟩).lower ∧ (cell13020 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13020 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13020 ⟨23,by decide⟩).lower ∧ (cell13020 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13020 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13020 ⟨24,by decide⟩).lower ∧ (cell13020 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13020 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13020 ⟨25,by decide⟩).lower ∧ (cell13020 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13020 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13020 ⟨26,by decide⟩).lower ∧ (cell13020 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13020 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13020 ⟨27,by decide⟩).lower ∧ (cell13020 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13020 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13020 ⟨28,by decide⟩).lower ∧ (cell13020 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13020 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13020 ⟨29,by decide⟩).lower ∧ (cell13020 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13020 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13020 ⟨30,by decide⟩).lower ∧ (cell13020 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13020 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13020 ⟨31,by decide⟩).lower ∧ (cell13020 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13020 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13020 ⟨32,by decide⟩).lower ∧ (cell13020 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13020 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13020 ⟨33,by decide⟩).lower ∧ (cell13020 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13020 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13020 ⟨34,by decide⟩).lower ∧ (cell13020 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13020 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13020 ⟨35,by decide⟩).lower ∧ (cell13020 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13020 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13020 ⟨36,by decide⟩).lower ∧ (cell13020 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13020 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13020 ⟨37,by decide⟩).lower ∧ (cell13020 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13020 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13020 ⟨38,by decide⟩).lower ∧ (cell13020 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13020 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13020 ⟨39,by decide⟩).lower ∧ (cell13020 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13020 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13020 ⟨40,by decide⟩).lower ∧ (cell13020 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13020 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13020 ⟨41,by decide⟩).lower ∧ (cell13020 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13020 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13020 ⟨42,by decide⟩).lower ∧ (cell13020 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13020 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13020 ⟨43,by decide⟩).lower ∧ (cell13020 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13020 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13020 ⟨44,by decide⟩).lower ∧ (cell13020 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13020 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13020 ⟨45,by decide⟩).lower ∧ (cell13020 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13020 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13020 ⟨46,by decide⟩).lower ∧ (cell13020 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13020 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13020 ⟨47,by decide⟩).lower ∧ (cell13020 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13020 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13020 ⟨48,by decide⟩).lower ∧ (cell13020 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13020 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13020 ⟨49,by decide⟩).lower ∧ (cell13020 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13020 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13020 ⟨50,by decide⟩).lower ∧ (cell13020 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13020 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13020 ⟨51,by decide⟩).lower ∧ (cell13020 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13020 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13020 ⟨52,by decide⟩).lower ∧ (cell13020 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13020 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13020 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13020 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13020,cell13020,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13020 i).lower ∧
    (cell13020 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13020 i).upper ≤ (0.532 : ℝ) ∧
    (cell13020 i).centre ≤ (0.1 : ℝ) ∧ (cell13020 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13020 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13020 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13020

/-! The local source numeric instances at 13020 have no network premises. -/
namespace BstLean.Part269.N13020
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13020)
open BstLean.Part268 (cell13020)

noncomputable def sourceNumerics13020 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13020 (cell13020 i)
      scalarRow13020.M scalarRow13020.H scalarRow13020.xi := by
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
    energy_allowance := scalarRow13020.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13020]
    centre_nonneg := (scalarRow13020.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13020])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13020
/-! Actual 13021 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13021 ≤ (1.035361215404 : ℝ) := by
  have hr : (114.109596441316 : ℝ) ≤ √(13021 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.109596441316 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13021 13021 (11 / 1000) ≤
    (0.008376919806 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13021) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.109596441316 : ℝ) ≤ √(13021 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13021)
  have hdiv : K / √(13021 : ℝ) ≤ K / 114.109596441316 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.109596441316 ≤ (0.008376919806 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13021.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13021 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13021 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13021 := gPlus_lower 13021
end BstLean.Part269.N13021

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13021
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035361215403 : ℝ) ≤ wn 13021 := by
  have hn : √(13021 : ℝ) ≤ 114.109596441317 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13021 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.109596441317 ≤ 2 / √(13021 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245565123 : ℝ) ≤ rhoBar 13021 BstLean.Part154.csC ∧
    rhoBar 13021 BstLean.Part154.csC ≤ 0.000245565503 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035361215403 : ℝ) / (1.295212 * 13021) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035361215404 : ℝ) / (1.29521 * 13021) := by gcongr
      _ ≤ (0.000245565503 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13021 BstLean.Part154.csC) ≤ 0.000982322315 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13021 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) ≤ 0.000187564369 ∧
    cc1 (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) ≤ 0.000119348498 ∧
    cc2 (rhoBar 13021 BstLean.Part154.csC) ≤ 0.000069282772 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13021 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13021 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13021 BstLean.Part154.csC * nuR (rhoBar 13021 BstLean.Part154.csC)) ≤ 0.000491146082 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245565503 : ℝ) * 0.000982322315 := by gcongr
      _ ≤ (0.000491146082 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13021 BstLean.Part154.csC) * nuR (rhoBar 13021 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982322315 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13021 BstLean.Part154.csC) * rhoBar 13021 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245565503 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245565503 / 2 + 0.399 * 0.000982322315 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187564369 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491146082 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119348498 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245565503 / 1.414213562 := by gcongr
      _ ≤ (0.000069282772 : ℝ) := by norm_num

end BstLean.Part269.N13021

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13021
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) ≤ 1.51928E-7 := by
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13021 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13021 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13021 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187564369 : ℝ) ^ 2 + 0.000119348498 ^ 2 + 3 * 0.000069282772 ^ 2 +
        2 * 0.797885 * 0.000187564369 * 0.000119348498 + 2 * 0.000187564369 * 0.000069282772 +
        4 * 0.797885 * 0.000119348498 * 0.000069282772 := by gcongr
    _ ≤ (1.51928E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13021 BstLean.Part154.csC Θ ≤ 0.002562258953 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13021 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13021 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13021 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035361215404 * 1.51928E-7 / (0.000245565123 : ℝ) := by gcongr
    _ ≤ 0.002562258953 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13021 BstLean.Part154.csC Θ ≤ 0.002841723417 + 0.000647439891 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13021 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13021 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035361215404 : ℝ) * ((2 * Θ * 0.000245565503 +
        (6863 / 10000) * 0.000245565503 * 13021 * 0.000982322315) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002841723417 + 0.000647439891 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13021 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13021 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13021 0.011 Θ ∧ gammaRatio 13021 0.011 Θ ≤ 0.000084419070 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13021 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035361215404 : ℝ) * 0.525 / ((1 - 0.011) * 13021) := by gcongr
      _ ≤ (0.000084419070 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13021 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13021 0.011 Θ) :=
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
    badAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13021 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13021 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13021 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13021 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13021 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13021 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13021 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13021 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13021 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13021 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035361215404 : ℝ) * 13021 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003224433178 + 0.003209698844 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13021

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13021
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13021 BstLean.Part154.csC) (piBar (rhoBar 13021 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13021 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13021 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13021 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13021 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13021 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13021 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13021 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13021 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13021 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13021 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051826370159 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13021) ≤ 0.010465706815 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13021 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035361215404)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010465706815 + 2 * 0.737676 / 13021) := by gcongr
    _ ≤ (0.051826370159 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13021 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13021

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13021
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517726994 : ℝ) ≤ plow 13021 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13021) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416125072)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345185951) : eMP 13021 0.011 xi bn ≤ 0.001158500062 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13021 : ℝ) * (1 - 0.011))) ≤ 0.000572856449 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345185951 / (13021 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572856449 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572856449 : ℝ) + 3.141593 * 0.052416125072 / (13021 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158500062 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416125072)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345185951) : PiBarMP 13021 12 0.011 xi bn ≤ 0.159231197467 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13021 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036676776726 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.480258194982 : ℝ) ≤ √((13021 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.109596441316 : ℝ) ≤ √(13021 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13021) ≤ 0.122096727158 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036676776726 + 0.052416125072 * 1.772454 / (2 * (113.480258194982 : ℝ))) * (1 + 0.001158500062) +
        8 / (13021 * 114.109596441316) + 0.122096727158 := by gcongr
    _ ≤ (0.159231197467 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416125072)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345185951) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280772051647) :
    parallelOracle 13021 0.011 xi bn cd ≤ 0.160196955306 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13021 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13021 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517726994 : ℝ) ≤ plow 13021 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.109596441316 : ℝ) ≤ √(13021 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280772051647 : ℝ) / (2 * 0.560517726994 * 114.109596441316)) * 0.159231197467 +
        0.280772051647 ^ 2 / (2 * 0.560517726994 * 114.109596441316) := by gcongr
    _ ≤ (0.160196955306 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052416125072) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345185951)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280772051647) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13021 13021 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517726994 : ℝ) ≤ plow 13021 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.109596441316 : ℝ) ≤ √(13021 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13021 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13021 Θ 1.22 ≤ 0.011621288142 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.109596441316 := by gcongr <;> linarith
      _ ≤ (0.011621288142 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13021 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13021 13021 0.011 ≤ 0.008376919806 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13021 13021 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13021 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13021 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13021 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13021 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160196955306 + 0.011621288142 + (0.008376919806 : ℝ) *
        (1 + 2 * (0.280772051647 + 0.011621288142) / (0.560517726994 * 114.109596441316))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13021]

end BstLean.Part269.N13021

/-! The original eight local profiles supply actual 13021 moment certificates. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13021 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052416125072 ∧
    0 ≤ bN 13021 BstLean.Part154.csC (groupTheta g) ∧ bN 13021 BstLean.Part154.csC (groupTheta g) ≤ 0.001345185951 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13021 13021 0.011
      (momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13021 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13021 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13021 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228945681488 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13021 0.011
      (momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13021 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13021
/-! The actual computed-centre upper energy formula at 13021. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13021

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13021)
open BstLean.Part268 (cell13021)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084605300859
  | 2 => 0.085533254621
  | 3 => 0.086457308462
  | 4 => 0.087378401187
  | 5 => 0.088297682360
  | 6 => 0.089216545343
  | 7 => 0.090136663781
  | 8 => 0.091060031618
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13021 13021 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13021 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13021

/-! Actual upper energy certificates on all 43 source endpoints at 13021. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13021)
open BstLean.Part268 (cell13021)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13021 (gMinus 13021) (1 - (cell13021 i).lower) ≤ 1 ∧
    energyUpper 13021 (gMinus 13021) (BstLean.Part211.gPlus 13021)
      (finiteEnergy 13021 13021 0.011) (1 - (cell13021 i).lower) ≤
      (cell13021 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨10,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨11,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨12,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨13,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨14,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨15,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨16,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨17,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨18,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨19,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨20,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨21,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨22,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨23,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨24,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨25,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨26,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨27,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨28,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨29,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨30,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨31,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨32,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨33,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨34,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨35,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨36,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨37,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨38,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨39,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨40,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨41,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨42,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨43,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨44,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨45,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨46,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨47,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨48,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨49,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨50,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨51,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13021) (by norm_num)
        (q := 1 - (cell13021 ⟨52,by decide⟩).lower)
        (by norm_num [cell13021]) (by norm_num [cell13021])
      exact ⟨E.1,E.2.trans (by norm_num [cell13021])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13021

/-! Source-cell containment and simple scalar guards at 13021. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13021)
open BstLean.Part268 (cell13021)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13021 ⟨10,by decide⟩).lower ∧ (cell13021 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13021 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13021 ⟨11,by decide⟩).lower ∧ (cell13021 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13021 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13021 ⟨12,by decide⟩).lower ∧ (cell13021 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13021 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13021 ⟨13,by decide⟩).lower ∧ (cell13021 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13021 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13021 ⟨14,by decide⟩).lower ∧ (cell13021 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13021 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13021 ⟨15,by decide⟩).lower ∧ (cell13021 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13021 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13021 ⟨16,by decide⟩).lower ∧ (cell13021 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13021 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13021 ⟨17,by decide⟩).lower ∧ (cell13021 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13021 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13021 ⟨18,by decide⟩).lower ∧ (cell13021 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13021 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13021 ⟨19,by decide⟩).lower ∧ (cell13021 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13021 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13021 ⟨20,by decide⟩).lower ∧ (cell13021 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13021 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13021 ⟨21,by decide⟩).lower ∧ (cell13021 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13021 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13021 ⟨22,by decide⟩).lower ∧ (cell13021 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13021 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13021 ⟨23,by decide⟩).lower ∧ (cell13021 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13021 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13021 ⟨24,by decide⟩).lower ∧ (cell13021 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13021 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13021 ⟨25,by decide⟩).lower ∧ (cell13021 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13021 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13021 ⟨26,by decide⟩).lower ∧ (cell13021 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13021 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13021 ⟨27,by decide⟩).lower ∧ (cell13021 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13021 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13021 ⟨28,by decide⟩).lower ∧ (cell13021 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13021 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13021 ⟨29,by decide⟩).lower ∧ (cell13021 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13021 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13021 ⟨30,by decide⟩).lower ∧ (cell13021 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13021 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13021 ⟨31,by decide⟩).lower ∧ (cell13021 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13021 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13021 ⟨32,by decide⟩).lower ∧ (cell13021 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13021 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13021 ⟨33,by decide⟩).lower ∧ (cell13021 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13021 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13021 ⟨34,by decide⟩).lower ∧ (cell13021 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13021 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13021 ⟨35,by decide⟩).lower ∧ (cell13021 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13021 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13021 ⟨36,by decide⟩).lower ∧ (cell13021 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13021 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13021 ⟨37,by decide⟩).lower ∧ (cell13021 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13021 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13021 ⟨38,by decide⟩).lower ∧ (cell13021 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13021 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13021 ⟨39,by decide⟩).lower ∧ (cell13021 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13021 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13021 ⟨40,by decide⟩).lower ∧ (cell13021 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13021 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13021 ⟨41,by decide⟩).lower ∧ (cell13021 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13021 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13021 ⟨42,by decide⟩).lower ∧ (cell13021 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13021 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13021 ⟨43,by decide⟩).lower ∧ (cell13021 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13021 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13021 ⟨44,by decide⟩).lower ∧ (cell13021 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13021 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13021 ⟨45,by decide⟩).lower ∧ (cell13021 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13021 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13021 ⟨46,by decide⟩).lower ∧ (cell13021 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13021 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13021 ⟨47,by decide⟩).lower ∧ (cell13021 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13021 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13021 ⟨48,by decide⟩).lower ∧ (cell13021 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13021 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13021 ⟨49,by decide⟩).lower ∧ (cell13021 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13021 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13021 ⟨50,by decide⟩).lower ∧ (cell13021 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13021 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13021 ⟨51,by decide⟩).lower ∧ (cell13021 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13021 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13021 ⟨52,by decide⟩).lower ∧ (cell13021 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13021 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13021 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13021 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13021,cell13021,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13021 i).lower ∧
    (cell13021 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13021 i).upper ≤ (0.532 : ℝ) ∧
    (cell13021 i).centre ≤ (0.1 : ℝ) ∧ (cell13021 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13021 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13021 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13021

/-! The local source numeric instances at 13021 have no network premises. -/
namespace BstLean.Part269.N13021
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13021)
open BstLean.Part268 (cell13021)

noncomputable def sourceNumerics13021 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13021 (cell13021 i)
      scalarRow13021.M scalarRow13021.H scalarRow13021.xi := by
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
    energy_allowance := scalarRow13021.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13021]
    centre_nonneg := (scalarRow13021.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13021])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13021
/-! Actual 13022 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13022 ≤ (1.035359845834 : ℝ) := by
  have hr : (114.113978109607 : ℝ) ≤ √(13022 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.113978109607 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13022 13022 (11 / 1000) ≤
    (0.008376598153 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13022) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.113978109607 : ℝ) ≤ √(13022 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13022)
  have hdiv : K / √(13022 : ℝ) ≤ K / 114.113978109607 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.113978109607 ≤ (0.008376598153 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13022.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13022 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13022 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13022 := gPlus_lower 13022
end BstLean.Part269.N13022

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13022
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035359845833 : ℝ) ≤ wn 13022 := by
  have hn : √(13022 : ℝ) ≤ 114.113978109608 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13022 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.113978109608 ≤ 2 / √(13022 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245545940 : ℝ) ≤ rhoBar 13022 BstLean.Part154.csC ∧
    rhoBar 13022 BstLean.Part154.csC ≤ 0.000245546320 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035359845833 : ℝ) / (1.295212 * 13022) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035359845834 : ℝ) / (1.29521 * 13022) := by gcongr
      _ ≤ (0.000245546320 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13022 BstLean.Part154.csC) ≤ 0.000982245573 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13022 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) ≤ 0.000187549716 ∧
    cc1 (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) ≤ 0.000119339175 ∧
    cc2 (rhoBar 13022 BstLean.Part154.csC) ≤ 0.000069277360 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13022 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13022 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13022 BstLean.Part154.csC * nuR (rhoBar 13022 BstLean.Part154.csC)) ≤ 0.000491107714 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245546320 : ℝ) * 0.000982245573 := by gcongr
      _ ≤ (0.000491107714 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13022 BstLean.Part154.csC) * nuR (rhoBar 13022 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982245573 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13022 BstLean.Part154.csC) * rhoBar 13022 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245546320 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245546320 / 2 + 0.399 * 0.000982245573 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187549716 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491107714 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119339175 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245546320 / 1.414213562 := by gcongr
      _ ≤ (0.000069277360 : ℝ) := by norm_num

end BstLean.Part269.N13022

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13022
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) ≤ 1.51904E-7 := by
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13022 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13022 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13022 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187549716 : ℝ) ^ 2 + 0.000119339175 ^ 2 + 3 * 0.000069277360 ^ 2 +
        2 * 0.797885 * 0.000187549716 * 0.000119339175 + 2 * 0.000187549716 * 0.000069277360 +
        4 * 0.797885 * 0.000119339175 * 0.000069277360 := by gcongr
    _ ≤ (1.51904E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13022 BstLean.Part154.csC Θ ≤ 0.002562050947 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13022 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13022 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13022 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035359845834 * 1.51904E-7 / (0.000245545940 : ℝ) := by gcongr
    _ ≤ 0.002562050947 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13022 BstLean.Part154.csC Θ ≤ 0.002841493891 + 0.000647388458 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13022 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13022 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035359845834 : ℝ) * ((2 * Θ * 0.000245546320 +
        (6863 / 10000) * 0.000245546320 * 13022 * 0.000982245573) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002841493891 + 0.000647388458 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13022 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13022 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13022 0.011 Θ ∧ gammaRatio 13022 0.011 Θ ≤ 0.000084412476 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13022 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035359845834 : ℝ) * 0.525 / ((1 - 0.011) * 13022) := by gcongr
      _ ≤ (0.000084412476 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13022 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13022 0.011 Θ) :=
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
    badAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13022 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13022 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13022 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13022 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13022 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13022 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13022 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13022 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13022 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13022 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035359845834 : ℝ) * 13022 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003224203652 + 0.003209439405 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13022

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13022
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13022 BstLean.Part154.csC) (piBar (rhoBar 13022 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13022 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13022 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13022 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13022 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13022 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13022 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13022 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13022 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13022 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13022 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051824358853 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13022) ≤ 0.010465304960 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13022 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035359845834)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010465304960 + 2 * 0.737676 / 13022) := by gcongr
    _ ≤ (0.051824358853 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13022 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13022

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13022
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517770012 : ℝ) ≤ plow 13022 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13022) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415759340)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345076748) : eMP 13022 0.011 xi bn ≤ 0.001158408494 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13022 : ℝ) * (1 - 0.011))) ≤ 0.000572811201 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001345076748 / (13022 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572811201 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572811201 : ℝ) + 3.141593 * 0.052415759340 / (13022 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158408494 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415759340)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345076748) : PiBarMP 13022 12 0.011 xi bn ≤ 0.159224996196 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13022 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036675287975 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.484615697459 : ℝ) ≤ √((13022 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.113978109607 : ℝ) ≤ √(13022 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13022) ≤ 0.122092038974 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036675287975 + 0.052415759340 * 1.772454 / (2 * (113.484615697459 : ℝ))) * (1 + 0.001158408494) +
        8 / (13022 * 114.113978109607) + 0.122092038974 := by gcongr
    _ ≤ (0.159224996196 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415759340)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345076748) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280769241609) :
    parallelOracle 13022 0.011 xi bn cd ≤ 0.160190687435 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13022 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13022 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517770012 : ℝ) ≤ plow 13022 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.113978109607 : ℝ) ≤ √(13022 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280769241609 : ℝ) / (2 * 0.560517770012 * 114.113978109607)) * 0.159224996196 +
        0.280769241609 ^ 2 / (2 * 0.560517770012 * 114.113978109607) := by gcongr
    _ ≤ (0.160190687435 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415759340) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001345076748)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280769241609) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13022 13022 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517770012 : ℝ) ≤ plow 13022 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.113978109607 : ℝ) ≤ √(13022 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13022 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13022 Θ 1.22 ≤ 0.011620841916 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.113978109607 := by gcongr <;> linarith
      _ ≤ (0.011620841916 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13022 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13022 13022 0.011 ≤ 0.008376598153 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13022 13022 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13022 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13022 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13022 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13022 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160190687435 + 0.011620841916 + (0.008376598153 : ℝ) *
        (1 + 2 * (0.280769241609 + 0.011620841916) / (0.560517770012 * 114.113978109607))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13022]

end BstLean.Part269.N13022

/-! The original eight local profiles supply actual 13022 moment certificates. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13022 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052415759340 ∧
    0 ≤ bN 13022 BstLean.Part154.csC (groupTheta g) ∧ bN 13022 BstLean.Part154.csC (groupTheta g) ≤ 0.001345076748 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13022 13022 0.011
      (momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13022 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13022 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13022 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228944882756 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13022 0.011
      (momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13022 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13022
/-! The actual computed-centre upper energy formula at 13022. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13022

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13022)
open BstLean.Part268 (cell13022)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084602699436
  | 2 => 0.085530619241
  | 3 => 0.086454634011
  | 4 => 0.087375681351
  | 5 => 0.088294909403
  | 6 => 0.089213709861
  | 7 => 0.090133754420
  | 8 => 0.091057034763
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13022 13022 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13022 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13022

/-! Actual upper energy certificates on all 43 source endpoints at 13022. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13022)
open BstLean.Part268 (cell13022)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13022 (gMinus 13022) (1 - (cell13022 i).lower) ≤ 1 ∧
    energyUpper 13022 (gMinus 13022) (BstLean.Part211.gPlus 13022)
      (finiteEnergy 13022 13022 0.011) (1 - (cell13022 i).lower) ≤
      (cell13022 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨10,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨11,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨12,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨13,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨14,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨15,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨16,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨17,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨18,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨19,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨20,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨21,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨22,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨23,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨24,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨25,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨26,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨27,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨28,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨29,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨30,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨31,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨32,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨33,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨34,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨35,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨36,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨37,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨38,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨39,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨40,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨41,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨42,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨43,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨44,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨45,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨46,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨47,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨48,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨49,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨50,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨51,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13022) (by norm_num)
        (q := 1 - (cell13022 ⟨52,by decide⟩).lower)
        (by norm_num [cell13022]) (by norm_num [cell13022])
      exact ⟨E.1,E.2.trans (by norm_num [cell13022])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13022

/-! Source-cell containment and simple scalar guards at 13022. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13022)
open BstLean.Part268 (cell13022)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13022 ⟨10,by decide⟩).lower ∧ (cell13022 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13022 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13022 ⟨11,by decide⟩).lower ∧ (cell13022 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13022 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13022 ⟨12,by decide⟩).lower ∧ (cell13022 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13022 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13022 ⟨13,by decide⟩).lower ∧ (cell13022 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13022 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13022 ⟨14,by decide⟩).lower ∧ (cell13022 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13022 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13022 ⟨15,by decide⟩).lower ∧ (cell13022 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13022 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13022 ⟨16,by decide⟩).lower ∧ (cell13022 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13022 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13022 ⟨17,by decide⟩).lower ∧ (cell13022 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13022 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13022 ⟨18,by decide⟩).lower ∧ (cell13022 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13022 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13022 ⟨19,by decide⟩).lower ∧ (cell13022 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13022 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13022 ⟨20,by decide⟩).lower ∧ (cell13022 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13022 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13022 ⟨21,by decide⟩).lower ∧ (cell13022 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13022 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13022 ⟨22,by decide⟩).lower ∧ (cell13022 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13022 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13022 ⟨23,by decide⟩).lower ∧ (cell13022 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13022 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13022 ⟨24,by decide⟩).lower ∧ (cell13022 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13022 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13022 ⟨25,by decide⟩).lower ∧ (cell13022 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13022 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13022 ⟨26,by decide⟩).lower ∧ (cell13022 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13022 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13022 ⟨27,by decide⟩).lower ∧ (cell13022 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13022 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13022 ⟨28,by decide⟩).lower ∧ (cell13022 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13022 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13022 ⟨29,by decide⟩).lower ∧ (cell13022 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13022 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13022 ⟨30,by decide⟩).lower ∧ (cell13022 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13022 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13022 ⟨31,by decide⟩).lower ∧ (cell13022 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13022 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13022 ⟨32,by decide⟩).lower ∧ (cell13022 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13022 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13022 ⟨33,by decide⟩).lower ∧ (cell13022 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13022 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13022 ⟨34,by decide⟩).lower ∧ (cell13022 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13022 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13022 ⟨35,by decide⟩).lower ∧ (cell13022 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13022 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13022 ⟨36,by decide⟩).lower ∧ (cell13022 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13022 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13022 ⟨37,by decide⟩).lower ∧ (cell13022 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13022 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13022 ⟨38,by decide⟩).lower ∧ (cell13022 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13022 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13022 ⟨39,by decide⟩).lower ∧ (cell13022 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13022 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13022 ⟨40,by decide⟩).lower ∧ (cell13022 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13022 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13022 ⟨41,by decide⟩).lower ∧ (cell13022 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13022 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13022 ⟨42,by decide⟩).lower ∧ (cell13022 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13022 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13022 ⟨43,by decide⟩).lower ∧ (cell13022 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13022 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13022 ⟨44,by decide⟩).lower ∧ (cell13022 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13022 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13022 ⟨45,by decide⟩).lower ∧ (cell13022 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13022 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13022 ⟨46,by decide⟩).lower ∧ (cell13022 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13022 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13022 ⟨47,by decide⟩).lower ∧ (cell13022 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13022 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13022 ⟨48,by decide⟩).lower ∧ (cell13022 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13022 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13022 ⟨49,by decide⟩).lower ∧ (cell13022 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13022 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13022 ⟨50,by decide⟩).lower ∧ (cell13022 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13022 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13022 ⟨51,by decide⟩).lower ∧ (cell13022 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13022 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13022 ⟨52,by decide⟩).lower ∧ (cell13022 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13022 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13022 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13022 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13022,cell13022,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13022 i).lower ∧
    (cell13022 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13022 i).upper ≤ (0.532 : ℝ) ∧
    (cell13022 i).centre ≤ (0.1 : ℝ) ∧ (cell13022 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13022 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13022 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13022

/-! The local source numeric instances at 13022 have no network premises. -/
namespace BstLean.Part269.N13022
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13022)
open BstLean.Part268 (cell13022)

noncomputable def sourceNumerics13022 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13022 (cell13022 i)
      scalarRow13022.M scalarRow13022.H scalarRow13022.xi := by
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
    energy_allowance := scalarRow13022.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13022]
    centre_nonneg := (scalarRow13022.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13022])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13022
/-! Actual 13023 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13023 ≤ (1.035358476422 : ℝ) := by
  have hr : (114.118359609661 : ℝ) ≤ √(13023 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.118359609661 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13023 13023 (11 / 1000) ≤
    (0.008376276536 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13023) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.118359609661 : ℝ) ≤ √(13023 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13023)
  have hdiv : K / √(13023 : ℝ) ≤ K / 114.118359609661 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.118359609661 ≤ (0.008376276536 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13023.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13023 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13023 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13023 := gPlus_lower 13023
end BstLean.Part269.N13023

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13023
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035358476421 : ℝ) ≤ wn 13023 := by
  have hn : √(13023 : ℝ) ≤ 114.118359609662 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13023 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.118359609662 ≤ 2 / √(13023 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245526761 : ℝ) ≤ rhoBar 13023 BstLean.Part154.csC ∧
    rhoBar 13023 BstLean.Part154.csC ≤ 0.000245527141 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035358476421 : ℝ) / (1.295212 * 13023) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035358476422 : ℝ) / (1.29521 * 13023) := by gcongr
      _ ≤ (0.000245527141 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13023 BstLean.Part154.csC) ≤ 0.000982168848 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13023 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) ≤ 0.000187535067 ∧
    cc1 (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) ≤ 0.000119329853 ∧
    cc2 (rhoBar 13023 BstLean.Part154.csC) ≤ 0.000069271949 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13023 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13023 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13023 BstLean.Part154.csC * nuR (rhoBar 13023 BstLean.Part154.csC)) ≤ 0.000491069353 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245527141 : ℝ) * 0.000982168848 := by gcongr
      _ ≤ (0.000491069353 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13023 BstLean.Part154.csC) * nuR (rhoBar 13023 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982168848 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13023 BstLean.Part154.csC) * rhoBar 13023 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245527141 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245527141 / 2 + 0.399 * 0.000982168848 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187535067 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491069353 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119329853 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245527141 / 1.414213562 := by gcongr
      _ ≤ (0.000069271949 : ℝ) := by norm_num

end BstLean.Part269.N13023

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13023
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) ≤ 1.51880E-7 := by
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13023 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13023 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13023 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187535067 : ℝ) ^ 2 + 0.000119329853 ^ 2 + 3 * 0.000069271949 ^ 2 +
        2 * 0.797885 * 0.000187535067 * 0.000119329853 + 2 * 0.000187535067 * 0.000069271949 +
        4 * 0.797885 * 0.000119329853 * 0.000069271949 := by gcongr
    _ ≤ (1.51880E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13023 BstLean.Part154.csC Θ ≤ 0.002561842869 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13023 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13023 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13023 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035358476422 * 1.51880E-7 / (0.000245526761 : ℝ) := by gcongr
    _ ≤ 0.002561842869 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13023 BstLean.Part154.csC Θ ≤ 0.002841264427 + 0.000647337036 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13023 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13023 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035358476422 : ℝ) * ((2 * Θ * 0.000245527141 +
        (6863 / 10000) * 0.000245527141 * 13023 * 0.000982168848) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002841264427 + 0.000647337036 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13023 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13023 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13023 0.011 Θ ∧ gammaRatio 13023 0.011 Θ ≤ 0.000084405882 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13023 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035358476422 : ℝ) * 0.525 / ((1 - 0.011) * 13023) := by gcongr
      _ ≤ (0.000084405882 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13023 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13023 0.011 Θ) :=
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
    badAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13023 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13023 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13023 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13023 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13023 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13023 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13023 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13023 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13023 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13023 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035358476422 : ℝ) * 13023 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003223974188 + 0.003209179905 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13023

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13023
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13023 BstLean.Part154.csC) (piBar (rhoBar 13023 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13023 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13023 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13023 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13023 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13023 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13023 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13023 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13023 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13023 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13023 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051822347779 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13023) ≤ 0.010464903151 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13023 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035358476422)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010464903151 + 2 * 0.737676 / 13023) := by gcongr
    _ ≤ (0.051822347779 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13023 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13023

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13023
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517813023 : ℝ) ≤ plow 13023 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13023) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393639)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344967507) : eMP 13023 0.011 xi bn ≤ 0.001158316917 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13023 : ℝ) * (1 - 0.011))) ≤ 0.000572765948 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344967507 / (13023 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572765948 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572765948 : ℝ) + 3.141593 * 0.052415393639 / (13023 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158316917 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393639)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344967507) : PiBarMP 13023 12 0.011 xi bn ≤ 0.159218794886 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13023 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036673798645 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.488973032625 : ℝ) ≤ √((13023 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.118359609661 : ℝ) ≤ √(13023 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13023) ≤ 0.122087351329 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036673798645 + 0.052415393639 * 1.772454 / (2 * (113.488973032625 : ℝ))) * (1 + 0.001158316917) +
        8 / (13023 * 114.118359609661) + 0.122087351329 := by gcongr
    _ ≤ (0.159218794886 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393639)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344967507) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280766431868) :
    parallelOracle 13023 0.011 xi bn cd ≤ 0.160184419534 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13023 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13023 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517813023 : ℝ) ≤ plow 13023 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.118359609661 : ℝ) ≤ √(13023 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280766431868 : ℝ) / (2 * 0.560517813023 * 114.118359609661)) * 0.159218794886 +
        0.280766431868 ^ 2 / (2 * 0.560517813023 * 114.118359609661) := by gcongr
    _ ≤ (0.160184419534 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415393639) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344967507)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280766431868) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13023 13023 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517813023 : ℝ) ≤ plow 13023 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.118359609661 : ℝ) ≤ √(13023 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13023 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13023 Θ 1.22 ≤ 0.011620395742 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.118359609661 := by gcongr <;> linarith
      _ ≤ (0.011620395742 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13023 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13023 13023 0.011 ≤ 0.008376276536 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13023 13023 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13023 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13023 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13023 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13023 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160184419534 + 0.011620395742 + (0.008376276536 : ℝ) *
        (1 + 2 * (0.280766431868 + 0.011620395742) / (0.560517813023 * 114.118359609661))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13023]

end BstLean.Part269.N13023

/-! The original eight local profiles supply actual 13023 moment certificates. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13023 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052415393639 ∧
    0 ≤ bN 13023 BstLean.Part154.csC (groupTheta g) ∧ bN 13023 BstLean.Part154.csC (groupTheta g) ≤ 0.001344967507 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13023 13023 0.011
      (momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13023 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13023 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13023 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228944084089 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13023 0.011
      (momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13023 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13023
/-! The actual computed-centre upper energy formula at 13023. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13023

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13023)
open BstLean.Part268 (cell13023)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084600098804
  | 2 => 0.085527984680
  | 3 => 0.086451960415
  | 4 => 0.087372962411
  | 5 => 0.088292137395
  | 6 => 0.089210875391
  | 7 => 0.090130846149
  | 8 => 0.091054039091
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13023 13023 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13023 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13023

/-! Actual upper energy certificates on all 43 source endpoints at 13023. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13023)
open BstLean.Part268 (cell13023)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13023 (gMinus 13023) (1 - (cell13023 i).lower) ≤ 1 ∧
    energyUpper 13023 (gMinus 13023) (BstLean.Part211.gPlus 13023)
      (finiteEnergy 13023 13023 0.011) (1 - (cell13023 i).lower) ≤
      (cell13023 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨10,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨11,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨12,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨13,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨14,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨15,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨16,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨17,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨18,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨19,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨20,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨21,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨22,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨23,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨24,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨25,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨26,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨27,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨28,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨29,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨30,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨31,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨32,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨33,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨34,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨35,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨36,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨37,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨38,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨39,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨40,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨41,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨42,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨43,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨44,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨45,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨46,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨47,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨48,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨49,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨50,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨51,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13023) (by norm_num)
        (q := 1 - (cell13023 ⟨52,by decide⟩).lower)
        (by norm_num [cell13023]) (by norm_num [cell13023])
      exact ⟨E.1,E.2.trans (by norm_num [cell13023])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13023

/-! Source-cell containment and simple scalar guards at 13023. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13023)
open BstLean.Part268 (cell13023)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13023 ⟨10,by decide⟩).lower ∧ (cell13023 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13023 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13023 ⟨11,by decide⟩).lower ∧ (cell13023 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13023 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13023 ⟨12,by decide⟩).lower ∧ (cell13023 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13023 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13023 ⟨13,by decide⟩).lower ∧ (cell13023 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13023 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13023 ⟨14,by decide⟩).lower ∧ (cell13023 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13023 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13023 ⟨15,by decide⟩).lower ∧ (cell13023 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13023 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13023 ⟨16,by decide⟩).lower ∧ (cell13023 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13023 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13023 ⟨17,by decide⟩).lower ∧ (cell13023 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13023 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13023 ⟨18,by decide⟩).lower ∧ (cell13023 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13023 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13023 ⟨19,by decide⟩).lower ∧ (cell13023 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13023 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13023 ⟨20,by decide⟩).lower ∧ (cell13023 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13023 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13023 ⟨21,by decide⟩).lower ∧ (cell13023 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13023 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13023 ⟨22,by decide⟩).lower ∧ (cell13023 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13023 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13023 ⟨23,by decide⟩).lower ∧ (cell13023 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13023 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13023 ⟨24,by decide⟩).lower ∧ (cell13023 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13023 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13023 ⟨25,by decide⟩).lower ∧ (cell13023 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13023 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13023 ⟨26,by decide⟩).lower ∧ (cell13023 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13023 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13023 ⟨27,by decide⟩).lower ∧ (cell13023 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13023 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13023 ⟨28,by decide⟩).lower ∧ (cell13023 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13023 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13023 ⟨29,by decide⟩).lower ∧ (cell13023 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13023 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13023 ⟨30,by decide⟩).lower ∧ (cell13023 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13023 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13023 ⟨31,by decide⟩).lower ∧ (cell13023 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13023 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13023 ⟨32,by decide⟩).lower ∧ (cell13023 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13023 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13023 ⟨33,by decide⟩).lower ∧ (cell13023 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13023 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13023 ⟨34,by decide⟩).lower ∧ (cell13023 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13023 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13023 ⟨35,by decide⟩).lower ∧ (cell13023 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13023 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13023 ⟨36,by decide⟩).lower ∧ (cell13023 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13023 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13023 ⟨37,by decide⟩).lower ∧ (cell13023 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13023 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13023 ⟨38,by decide⟩).lower ∧ (cell13023 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13023 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13023 ⟨39,by decide⟩).lower ∧ (cell13023 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13023 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13023 ⟨40,by decide⟩).lower ∧ (cell13023 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13023 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13023 ⟨41,by decide⟩).lower ∧ (cell13023 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13023 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13023 ⟨42,by decide⟩).lower ∧ (cell13023 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13023 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13023 ⟨43,by decide⟩).lower ∧ (cell13023 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13023 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13023 ⟨44,by decide⟩).lower ∧ (cell13023 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13023 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13023 ⟨45,by decide⟩).lower ∧ (cell13023 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13023 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13023 ⟨46,by decide⟩).lower ∧ (cell13023 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13023 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13023 ⟨47,by decide⟩).lower ∧ (cell13023 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13023 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13023 ⟨48,by decide⟩).lower ∧ (cell13023 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13023 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13023 ⟨49,by decide⟩).lower ∧ (cell13023 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13023 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13023 ⟨50,by decide⟩).lower ∧ (cell13023 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13023 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13023 ⟨51,by decide⟩).lower ∧ (cell13023 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13023 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13023 ⟨52,by decide⟩).lower ∧ (cell13023 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13023 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13023 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13023 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13023,cell13023,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13023 i).lower ∧
    (cell13023 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13023 i).upper ≤ (0.532 : ℝ) ∧
    (cell13023 i).centre ≤ (0.1 : ℝ) ∧ (cell13023 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13023 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13023 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13023

/-! The local source numeric instances at 13023 have no network premises. -/
namespace BstLean.Part269.N13023
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13023)
open BstLean.Part268 (cell13023)

noncomputable def sourceNumerics13023 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13023 (cell13023 i)
      scalarRow13023.M scalarRow13023.H scalarRow13023.xi := by
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
    energy_allowance := scalarRow13023.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13023]
    centre_nonneg := (scalarRow13023.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13023])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13023
/-! Actual 13024 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13024 ≤ (1.035357107169 : ℝ) := by
  have hr : (114.122740941496 : ℝ) ≤ √(13024 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.122740941496 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13024 13024 (11 / 1000) ≤
    (0.008375954957 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13024) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.122740941496 : ℝ) ≤ √(13024 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13024)
  have hdiv : K / √(13024 : ℝ) ≤ K / 114.122740941496 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.122740941496 ≤ (0.008375954957 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13024.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13024 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13024 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13024 := gPlus_lower 13024
end BstLean.Part269.N13024

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13024
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035357107168 : ℝ) ≤ wn 13024 := by
  have hn : √(13024 : ℝ) ≤ 114.122740941497 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13024 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.122740941497 ≤ 2 / √(13024 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245507584 : ℝ) ≤ rhoBar 13024 BstLean.Part154.csC ∧
    rhoBar 13024 BstLean.Part154.csC ≤ 0.000245507964 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035357107168 : ℝ) / (1.295212 * 13024) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035357107169 : ℝ) / (1.29521 * 13024) := by gcongr
      _ ≤ (0.000245507964 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13024 BstLean.Part154.csC) ≤ 0.000982092131 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13024 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) ≤ 0.000187520418 ∧
    cc1 (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) ≤ 0.000119320533 ∧
    cc2 (rhoBar 13024 BstLean.Part154.csC) ≤ 0.000069266539 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13024 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13024 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13024 BstLean.Part154.csC * nuR (rhoBar 13024 BstLean.Part154.csC)) ≤ 0.000491030997 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245507964 : ℝ) * 0.000982092131 := by gcongr
      _ ≤ (0.000491030997 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13024 BstLean.Part154.csC) * nuR (rhoBar 13024 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000982092131 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13024 BstLean.Part154.csC) * rhoBar 13024 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245507964 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245507964 / 2 + 0.399 * 0.000982092131 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187520418 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491030997 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119320533 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245507964 / 1.414213562 := by gcongr
      _ ≤ (0.000069266539 : ℝ) := by norm_num

end BstLean.Part269.N13024

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13024
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) ≤ 1.51856E-7 := by
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13024 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13024 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13024 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187520418 : ℝ) ^ 2 + 0.000119320533 ^ 2 + 3 * 0.000069266539 ^ 2 +
        2 * 0.797885 * 0.000187520418 * 0.000119320533 + 2 * 0.000187520418 * 0.000069266539 +
        4 * 0.797885 * 0.000119320533 * 0.000069266539 := by gcongr
    _ ≤ (1.51856E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13024 BstLean.Part154.csC Θ ≤ 0.002561634738 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13024 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13024 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13024 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035357107169 * 1.51856E-7 / (0.000245507584 : ℝ) := by gcongr
    _ ≤ 0.002561634738 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13024 BstLean.Part154.csC Θ ≤ 0.002841034977 + 0.000647285620 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13024 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13024 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035357107169 : ℝ) * ((2 * Θ * 0.000245507964 +
        (6863 / 10000) * 0.000245507964 * 13024 * 0.000982092131) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002841034977 + 0.000647285620 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13024 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13024 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13024 0.011 Θ ∧ gammaRatio 13024 0.011 Θ ≤ 0.000084399290 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13024 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035357107169 : ℝ) * 0.525 / ((1 - 0.011) * 13024) := by gcongr
      _ ≤ (0.000084399290 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13024 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13024 0.011 Θ) :=
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
    badAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13024 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13024 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13024 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13024 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13024 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13024 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13024 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13024 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13024 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13024 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035357107169 : ℝ) * 13024 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003223744738 + 0.003208920358 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13024

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13024
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13024 BstLean.Part154.csC) (piBar (rhoBar 13024 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13024 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13024 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13024 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13024 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13024 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13024 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13024 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13024 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13024 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13024 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051820336942 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13024) ≤ 0.010464501389 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13024 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035357107169)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010464501389 + 2 * 0.737676 / 13024) := by gcongr
    _ ≤ (0.051820336942 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13024 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13024

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13024
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517856027 : ℝ) ≤ plow 13024 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13024) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344858238) : eMP 13024 0.011 xi bn ≤ 0.001158225336 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13024 : ℝ) * (1 - 0.011))) ≤ 0.000572720693 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001344858238 / (13024 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000572720693 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000572720693 : ℝ) + 3.141593 * 0.052415027926 / (13024 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001158225336 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344858238) : PiBarMP 13024 12 0.011 xi bn ≤ 0.159212593676 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13024 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036672308872 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.493330200501 : ℝ) ≤ √((13024 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.122740941496 : ℝ) ≤ √(13024 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13024) ≤ 0.122082664225 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036672308872 + 0.052415027926 * 1.772454 / (2 * (113.493330200501 : ℝ))) * (1 + 0.001158225336) +
        8 / (13024 * 114.122740941496) + 0.122082664225 := by gcongr
    _ ≤ (0.159212593676 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344858238) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280763622334) :
    parallelOracle 13024 0.011 xi bn cd ≤ 0.160178151741 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13024 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13024 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517856027 : ℝ) ≤ plow 13024 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.122740941496 : ℝ) ≤ √(13024 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280763622334 : ℝ) / (2 * 0.560517856027 * 114.122740941496)) * 0.159212593676 +
        0.280763622334 ^ 2 / (2 * 0.560517856027 * 114.122740941496) := by gcongr
    _ ≤ (0.160178151741 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052415027926) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001344858238)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280763622334) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13024 13024 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517856027 : ℝ) ≤ plow 13024 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.122740941496 : ℝ) ≤ √(13024 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13024 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13024 Θ 1.22 ≤ 0.011619949618 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.122740941496 := by gcongr <;> linarith
      _ ≤ (0.011619949618 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13024 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13024 13024 0.011 ≤ 0.008375954957 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13024 13024 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13024 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13024 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13024 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13024 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160178151741 + 0.011619949618 + (0.008375954957 : ℝ) *
        (1 + 2 * (0.280763622334 + 0.011619949618) / (0.560517856027 * 114.122740941496))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13024]

end BstLean.Part269.N13024

/-! The original eight local profiles supply actual 13024 moment certificates. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13024 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052415027926 ∧
    0 ≤ bN 13024 BstLean.Part154.csC (groupTheta g) ∧ bN 13024 BstLean.Part154.csC (groupTheta g) ≤ 0.001344858238 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13024 13024 0.011
      (momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13024 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13024 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13024 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228943285392 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13024 0.011
      (momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13024 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13024
/-! The actual computed-centre upper energy formula at 13024. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13024

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13024)
open BstLean.Part268 (cell13024)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084597498963
  | 2 => 0.085525350938
  | 3 => 0.086449287670
  | 4 => 0.087370244367
  | 5 => 0.088289366334
  | 6 => 0.089208041932
  | 7 => 0.090127938965
  | 8 => 0.091051044601
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13024 13024 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13024 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13024

/-! Actual upper energy certificates on all 43 source endpoints at 13024. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13024)
open BstLean.Part268 (cell13024)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13024 (gMinus 13024) (1 - (cell13024 i).lower) ≤ 1 ∧
    energyUpper 13024 (gMinus 13024) (BstLean.Part211.gPlus 13024)
      (finiteEnergy 13024 13024 0.011) (1 - (cell13024 i).lower) ≤
      (cell13024 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨10,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨11,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨12,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨13,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨14,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨15,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨16,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨17,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨18,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨19,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨20,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨21,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨22,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨23,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨24,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨25,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨26,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨27,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨28,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨29,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨30,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨31,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨32,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨33,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨34,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨35,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨36,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨37,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨38,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨39,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨40,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨41,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨42,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨43,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨44,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨45,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨46,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨47,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨48,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨49,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨50,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨51,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13024) (by norm_num)
        (q := 1 - (cell13024 ⟨52,by decide⟩).lower)
        (by norm_num [cell13024]) (by norm_num [cell13024])
      exact ⟨E.1,E.2.trans (by norm_num [cell13024])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13024

/-! Source-cell containment and simple scalar guards at 13024. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13024)
open BstLean.Part268 (cell13024)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13024 ⟨10,by decide⟩).lower ∧ (cell13024 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13024 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13024 ⟨11,by decide⟩).lower ∧ (cell13024 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13024 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13024 ⟨12,by decide⟩).lower ∧ (cell13024 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13024 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13024 ⟨13,by decide⟩).lower ∧ (cell13024 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13024 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13024 ⟨14,by decide⟩).lower ∧ (cell13024 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13024 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13024 ⟨15,by decide⟩).lower ∧ (cell13024 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13024 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13024 ⟨16,by decide⟩).lower ∧ (cell13024 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13024 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13024 ⟨17,by decide⟩).lower ∧ (cell13024 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13024 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13024 ⟨18,by decide⟩).lower ∧ (cell13024 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13024 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13024 ⟨19,by decide⟩).lower ∧ (cell13024 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13024 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13024 ⟨20,by decide⟩).lower ∧ (cell13024 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13024 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13024 ⟨21,by decide⟩).lower ∧ (cell13024 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13024 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13024 ⟨22,by decide⟩).lower ∧ (cell13024 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13024 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13024 ⟨23,by decide⟩).lower ∧ (cell13024 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13024 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13024 ⟨24,by decide⟩).lower ∧ (cell13024 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13024 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13024 ⟨25,by decide⟩).lower ∧ (cell13024 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13024 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13024 ⟨26,by decide⟩).lower ∧ (cell13024 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13024 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13024 ⟨27,by decide⟩).lower ∧ (cell13024 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13024 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13024 ⟨28,by decide⟩).lower ∧ (cell13024 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13024 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13024 ⟨29,by decide⟩).lower ∧ (cell13024 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13024 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13024 ⟨30,by decide⟩).lower ∧ (cell13024 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13024 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13024 ⟨31,by decide⟩).lower ∧ (cell13024 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13024 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13024 ⟨32,by decide⟩).lower ∧ (cell13024 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13024 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13024 ⟨33,by decide⟩).lower ∧ (cell13024 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13024 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13024 ⟨34,by decide⟩).lower ∧ (cell13024 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13024 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13024 ⟨35,by decide⟩).lower ∧ (cell13024 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13024 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13024 ⟨36,by decide⟩).lower ∧ (cell13024 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13024 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13024 ⟨37,by decide⟩).lower ∧ (cell13024 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13024 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13024 ⟨38,by decide⟩).lower ∧ (cell13024 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13024 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13024 ⟨39,by decide⟩).lower ∧ (cell13024 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13024 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13024 ⟨40,by decide⟩).lower ∧ (cell13024 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13024 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13024 ⟨41,by decide⟩).lower ∧ (cell13024 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13024 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13024 ⟨42,by decide⟩).lower ∧ (cell13024 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13024 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13024 ⟨43,by decide⟩).lower ∧ (cell13024 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13024 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13024 ⟨44,by decide⟩).lower ∧ (cell13024 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13024 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13024 ⟨45,by decide⟩).lower ∧ (cell13024 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13024 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13024 ⟨46,by decide⟩).lower ∧ (cell13024 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13024 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13024 ⟨47,by decide⟩).lower ∧ (cell13024 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13024 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13024 ⟨48,by decide⟩).lower ∧ (cell13024 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13024 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13024 ⟨49,by decide⟩).lower ∧ (cell13024 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13024 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13024 ⟨50,by decide⟩).lower ∧ (cell13024 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13024 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13024 ⟨51,by decide⟩).lower ∧ (cell13024 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13024 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13024 ⟨52,by decide⟩).lower ∧ (cell13024 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13024 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13024 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13024 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13024,cell13024,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13024 i).lower ∧
    (cell13024 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13024 i).upper ≤ (0.532 : ℝ) ∧
    (cell13024 i).centre ≤ (0.1 : ℝ) ∧ (cell13024 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13024 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13024 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13024

/-! The local source numeric instances at 13024 have no network premises. -/
namespace BstLean.Part269.N13024
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13024)
open BstLean.Part268 (cell13024)

noncomputable def sourceNumerics13024 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13024 (cell13024 i)
      scalarRow13024.M scalarRow13024.H scalarRow13024.xi := by
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
    energy_allowance := scalarRow13024.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13024]
    centre_nonneg := (scalarRow13024.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13024])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13024