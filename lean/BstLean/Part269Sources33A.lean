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
import BstLean.Part269Direction33
import BstLean.Part269Shared33
import BstLean.Part269Finite
import BstLean.Part269Rows33
import BstLean.Part269Source
/-! Actual 13175 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13175 ≤ (1.035152152663 : ℝ) := by
  have hr : (114.782402832489 : ℝ) ≤ √(13175 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.782402832489 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13175 13175 (11 / 1000) ≤
    (0.008327817445 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13175) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.782402832489 : ℝ) ≤ √(13175 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13175)
  have hdiv : K / √(13175 : ℝ) ≤ K / 114.782402832489 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.782402832489 ≤ (0.008327817445 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13175.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13175 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13175 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13175 := gPlus_lower 13175
end BstLean.Part269.N13175

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13175
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035152152662 : ℝ) ≤ wn 13175 := by
  have hn : √(13175 : ℝ) ≤ 114.782402832490 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13175 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.782402832490 ≤ 2 / √(13175 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242645754 : ℝ) ≤ rhoBar 13175 BstLean.Part154.csC ∧
    rhoBar 13175 BstLean.Part154.csC ≤ 0.000242646130 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035152152662 : ℝ) / (1.295212 * 13175) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035152152663 : ℝ) / (1.29521 * 13175) := by gcongr
      _ ≤ (0.000242646130 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13175 BstLean.Part154.csC) ≤ 0.000970643398 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13175 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) ≤ 0.000185334435 ∧
    cc1 (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) ≤ 0.000117929597 ∧
    cc2 (rhoBar 13175 BstLean.Part154.csC) ≤ 0.000068459113 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13175 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13175 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13175 BstLean.Part154.csC * nuR (rhoBar 13175 BstLean.Part154.csC)) ≤ 0.000485306980 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242646130 : ℝ) * 0.000970643398 := by gcongr
      _ ≤ (0.000485306980 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13175 BstLean.Part154.csC) * nuR (rhoBar 13175 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970643398 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13175 BstLean.Part154.csC) * rhoBar 13175 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242646130 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242646130 / 2 + 0.399 * 0.000970643398 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185334435 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485306980 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117929597 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242646130 / 1.414213562 := by gcongr
      _ ≤ (0.000068459113 : ℝ) := by norm_num

end BstLean.Part269.N13175

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13175
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) ≤ 1.48337E-7 := by
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13175 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13175 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13175 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185334435 : ℝ) ^ 2 + 0.000117929597 ^ 2 + 3 * 0.000068459113 ^ 2 +
        2 * 0.797885 * 0.000185334435 * 0.000117929597 + 2 * 0.000185334435 * 0.000068459113 +
        4 * 0.797885 * 0.000117929597 * 0.000068459113 := by gcongr
    _ ≤ (1.48337E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13175 BstLean.Part154.csC Θ ≤ 0.002531284597 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13175 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13175 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13175 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035152152663 * 1.48337E-7 / (0.000242645754 : ℝ) := by gcongr
    _ ≤ 0.002531284597 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13175 BstLean.Part154.csC Θ ≤ 0.002806804056 + 0.000639613709 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13175 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13175 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035152152663 : ℝ) * ((2 * Θ * 0.000242646130 +
        (6863 / 10000) * 0.000242646130 * 13175 * 0.000970643398) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002806804056 + 0.000639613709 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13175 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13175 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13175 0.011 Θ ∧ gammaRatio 13175 0.011 Θ ≤ 0.000083415465 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13175 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035152152663 : ℝ) * 0.525 / ((1 - 0.011) * 13175) := by gcongr
      _ ≤ (0.000083415465 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13175 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13175 0.011 Θ) :=
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
    badAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13175 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13175 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13175 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13175 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13175 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13175 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13175 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13175 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13175 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13175 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035152152663 : ℝ) * 13175 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003124280256 + 0.003170898306 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13175

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13175
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13175 BstLean.Part154.csC) (piBar (rhoBar 13175 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13175 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13175 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13175 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13175 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13175 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13175 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13175 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13175 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13175 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13175 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051519351089 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13175) ≤ 0.010404361223 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13175 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035152152663)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010404361223 + 2 * 0.737676 / 13175) := by gcongr
    _ ≤ (0.051519351089 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13175 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13175

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13175
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524274747 : ℝ) ≤ plow 13175 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13175) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295601867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328924414) : eMP 13175 0.011 xi bn ≤ 0.001144700422 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13175 : ℝ) * (1 - 0.011))) ≤ 0.000566045892 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328924414 / (13175 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566045892 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566045892 : ℝ) + 3.141593 * 0.052295601867 / (13175 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144700422 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295601867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328924414) : PiBarMP 13175 12 0.011 xi bn ≤ 0.158288957028 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13175 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036454415563 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.149353918451 : ℝ) ≤ √((13175 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.782402832489 : ℝ) ≤ √(13175 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13175) ≤ 0.121381047260 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036454415563 + 0.052295601867 * 1.772454 / (2 * (114.149353918451 : ℝ))) * (1 + 0.001144700422) +
        8 / (13175 * 114.782402832489) + 0.121381047260 := by gcongr
    _ ≤ (0.158288957028 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295601867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328924414) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280201667562) :
    parallelOracle 13175 0.011 xi bn cd ≤ 0.159243798547 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13175 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13175 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524274747 : ℝ) ≤ plow 13175 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.782402832489 : ℝ) ≤ √(13175 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280201667562 : ℝ) / (2 * 0.560524274747 * 114.782402832489)) * 0.158288957028 +
        0.280201667562 ^ 2 / (2 * 0.560524274747 * 114.782402832489) := by gcongr
    _ ≤ (0.159243798547 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295601867) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328924414)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280201667562) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13175 13175 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524274747 : ℝ) ≤ plow 13175 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.782402832489 : ℝ) ≤ √(13175 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13175 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13175 Θ 1.22 ≤ 0.011553169017 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.782402832489 := by gcongr <;> linarith
      _ ≤ (0.011553169017 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13175 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13175 13175 0.011 ≤ 0.008327817445 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13175 13175 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13175 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13175 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13175 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13175 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159243798547 + 0.011553169017 + (0.008327817445 : ℝ) *
        (1 + 2 * (0.280201667562 + 0.011553169017) / (0.560524274747 * 114.782402832489))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13175]

end BstLean.Part269.N13175

/-! The original eight local profiles supply actual 13175 moment certificates. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13175 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052295601867 ∧
    0 ≤ bN 13175 BstLean.Part154.csC (groupTheta g) ∧ bN 13175 BstLean.Part154.csC (groupTheta g) ≤ 0.001328924414 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13175 13175 0.011
      (momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13175 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13175 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13175 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228682316473 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13175 0.011
      (momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13175 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13175
/-! The actual computed-centre upper energy formula at 13175. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13175

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13175)
open BstLean.Part268 (cell13175)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084213591871
  | 2 => 0.085136622744
  | 3 => 0.086055040117
  | 4 => 0.086969613327
  | 5 => 0.087881291112
  | 6 => 0.088791230452
  | 7 => 0.089700828547
  | 8 => 0.090611758058
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13175 13175 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13175 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13175

/-! Actual upper energy certificates on all 43 source endpoints at 13175. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13175)
open BstLean.Part268 (cell13175)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13175 (gMinus 13175) (1 - (cell13175 i).lower) ≤ 1 ∧
    energyUpper 13175 (gMinus 13175) (BstLean.Part211.gPlus 13175)
      (finiteEnergy 13175 13175 0.011) (1 - (cell13175 i).lower) ≤
      (cell13175 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨10,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨11,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨12,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨13,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨14,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨15,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨16,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨17,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨18,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨19,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨20,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨21,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨22,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨23,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨24,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨25,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨26,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨27,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨28,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨29,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨30,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨31,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨32,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨33,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨34,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨35,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨36,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨37,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨38,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨39,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨40,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨41,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨42,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨43,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨44,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨45,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨46,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨47,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨48,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨49,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨50,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨51,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13175) (by norm_num)
        (q := 1 - (cell13175 ⟨52,by decide⟩).lower)
        (by norm_num [cell13175]) (by norm_num [cell13175])
      exact ⟨E.1,E.2.trans (by norm_num [cell13175])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13175

/-! Source-cell containment and simple scalar guards at 13175. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13175)
open BstLean.Part268 (cell13175)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13175 ⟨10,by decide⟩).lower ∧ (cell13175 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13175 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13175 ⟨11,by decide⟩).lower ∧ (cell13175 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13175 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13175 ⟨12,by decide⟩).lower ∧ (cell13175 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13175 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13175 ⟨13,by decide⟩).lower ∧ (cell13175 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13175 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13175 ⟨14,by decide⟩).lower ∧ (cell13175 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13175 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13175 ⟨15,by decide⟩).lower ∧ (cell13175 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13175 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13175 ⟨16,by decide⟩).lower ∧ (cell13175 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13175 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13175 ⟨17,by decide⟩).lower ∧ (cell13175 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13175 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13175 ⟨18,by decide⟩).lower ∧ (cell13175 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13175 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13175 ⟨19,by decide⟩).lower ∧ (cell13175 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13175 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13175 ⟨20,by decide⟩).lower ∧ (cell13175 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13175 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13175 ⟨21,by decide⟩).lower ∧ (cell13175 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13175 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13175 ⟨22,by decide⟩).lower ∧ (cell13175 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13175 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13175 ⟨23,by decide⟩).lower ∧ (cell13175 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13175 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13175 ⟨24,by decide⟩).lower ∧ (cell13175 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13175 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13175 ⟨25,by decide⟩).lower ∧ (cell13175 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13175 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13175 ⟨26,by decide⟩).lower ∧ (cell13175 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13175 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13175 ⟨27,by decide⟩).lower ∧ (cell13175 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13175 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13175 ⟨28,by decide⟩).lower ∧ (cell13175 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13175 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13175 ⟨29,by decide⟩).lower ∧ (cell13175 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13175 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13175 ⟨30,by decide⟩).lower ∧ (cell13175 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13175 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13175 ⟨31,by decide⟩).lower ∧ (cell13175 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13175 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13175 ⟨32,by decide⟩).lower ∧ (cell13175 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13175 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13175 ⟨33,by decide⟩).lower ∧ (cell13175 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13175 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13175 ⟨34,by decide⟩).lower ∧ (cell13175 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13175 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13175 ⟨35,by decide⟩).lower ∧ (cell13175 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13175 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13175 ⟨36,by decide⟩).lower ∧ (cell13175 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13175 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13175 ⟨37,by decide⟩).lower ∧ (cell13175 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13175 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13175 ⟨38,by decide⟩).lower ∧ (cell13175 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13175 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13175 ⟨39,by decide⟩).lower ∧ (cell13175 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13175 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13175 ⟨40,by decide⟩).lower ∧ (cell13175 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13175 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13175 ⟨41,by decide⟩).lower ∧ (cell13175 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13175 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13175 ⟨42,by decide⟩).lower ∧ (cell13175 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13175 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13175 ⟨43,by decide⟩).lower ∧ (cell13175 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13175 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13175 ⟨44,by decide⟩).lower ∧ (cell13175 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13175 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13175 ⟨45,by decide⟩).lower ∧ (cell13175 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13175 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13175 ⟨46,by decide⟩).lower ∧ (cell13175 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13175 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13175 ⟨47,by decide⟩).lower ∧ (cell13175 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13175 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13175 ⟨48,by decide⟩).lower ∧ (cell13175 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13175 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13175 ⟨49,by decide⟩).lower ∧ (cell13175 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13175 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13175 ⟨50,by decide⟩).lower ∧ (cell13175 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13175 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13175 ⟨51,by decide⟩).lower ∧ (cell13175 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13175 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13175 ⟨52,by decide⟩).lower ∧ (cell13175 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13175 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13175 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13175 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13175,cell13175,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13175 i).lower ∧
    (cell13175 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13175 i).upper ≤ (0.532 : ℝ) ∧
    (cell13175 i).centre ≤ (0.1 : ℝ) ∧ (cell13175 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13175 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13175 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13175

/-! The local source numeric instances at 13175 have no network premises. -/
namespace BstLean.Part269.N13175
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13175)
open BstLean.Part268 (cell13175)

noncomputable def sourceNumerics13175 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13175 (cell13175 i)
      scalarRow13175.M scalarRow13175.H scalarRow13175.xi := by
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
    energy_allowance := scalarRow13175.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13175]
    centre_nonneg := (scalarRow13175.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13175])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13175
/-! Actual 13176 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13176 ≤ (1.035150807171 : ℝ) := by
  have hr : (114.786758818253 : ℝ) ≤ √(13176 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.786758818253 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13176 13176 (11 / 1000) ≤
    (0.008327501414 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13176) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.786758818253 : ℝ) ≤ √(13176 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13176)
  have hdiv : K / √(13176 : ℝ) ≤ K / 114.786758818253 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.786758818253 ≤ (0.008327501414 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13176.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13176 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13176 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13176 := gPlus_lower 13176
end BstLean.Part269.N13176

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13176
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035150807170 : ℝ) ≤ wn 13176 := by
  have hn : √(13176 : ℝ) ≤ 114.786758818254 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13176 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.786758818254 ≤ 2 / √(13176 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242627023 : ℝ) ≤ rhoBar 13176 BstLean.Part154.csC ∧
    rhoBar 13176 BstLean.Part154.csC ≤ 0.000242627399 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035150807170 : ℝ) / (1.295212 * 13176) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035150807171 : ℝ) / (1.29521 * 13176) := by gcongr
      _ ≤ (0.000242627399 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13176 BstLean.Part154.csC) ≤ 0.000970568465 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13176 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) ≤ 0.000185320128 ∧
    cc1 (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) ≤ 0.000117920493 ∧
    cc2 (rhoBar 13176 BstLean.Part154.csC) ≤ 0.000068453829 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13176 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13176 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13176 BstLean.Part154.csC * nuR (rhoBar 13176 BstLean.Part154.csC)) ≤ 0.000485269516 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242627399 : ℝ) * 0.000970568465 := by gcongr
      _ ≤ (0.000485269516 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13176 BstLean.Part154.csC) * nuR (rhoBar 13176 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970568465 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13176 BstLean.Part154.csC) * rhoBar 13176 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242627399 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242627399 / 2 + 0.399 * 0.000970568465 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185320128 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485269516 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117920493 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242627399 / 1.414213562 := by gcongr
      _ ≤ (0.000068453829 : ℝ) := by norm_num

end BstLean.Part269.N13176

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13176
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) ≤ 1.48314E-7 := by
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13176 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13176 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13176 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185320128 : ℝ) ^ 2 + 0.000117920493 ^ 2 + 3 * 0.000068453829 ^ 2 +
        2 * 0.797885 * 0.000185320128 * 0.000117920493 + 2 * 0.000185320128 * 0.000068453829 +
        4 * 0.797885 * 0.000117920493 * 0.000068453829 := by gcongr
    _ ≤ (1.48314E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13176 BstLean.Part154.csC Θ ≤ 0.002531084212 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13176 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13176 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13176 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035150807171 * 1.48314E-7 / (0.000242627023 : ℝ) := by gcongr
    _ ≤ 0.002531084212 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13176 BstLean.Part154.csC Θ ≤ 0.002806580078 + 0.000639563503 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13176 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13176 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035150807171 : ℝ) * ((2 * Θ * 0.000242627399 +
        (6863 / 10000) * 0.000242627399 * 13176 * 0.000970568465) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002806580078 + 0.000639563503 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13176 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13176 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13176 0.011 Θ ∧ gammaRatio 13176 0.011 Θ ≤ 0.000083409026 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13176 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035150807171 : ℝ) * 0.525 / ((1 - 0.011) * 13176) := by gcongr
      _ ≤ (0.000083409026 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13176 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13176 0.011 Θ) :=
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
    badAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13176 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13176 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13176 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13176 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13176 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13176 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13176 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13176 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13176 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13176 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035150807171 : ℝ) * 13176 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003124056278 + 0.003170647715 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13176

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13176
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13176 BstLean.Part154.csC) (piBar (rhoBar 13176 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13176 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13176 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13176 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13176 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13176 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13176 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13176 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13176 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13176 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13176 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051517375189 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13176) ≤ 0.010403966393 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13176 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035150807171)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010403966393 + 2 * 0.737676 / 13176) := by gcongr
    _ ≤ (0.051517375189 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13176 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13176

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13176
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524316765 : ℝ) ≤ plow 13176 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13176) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295246329)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328819212) : eMP 13176 0.011 xi bn ≤ 0.001144611610 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13176 : ℝ) * (1 - 0.011))) ≤ 0.000566002007 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328819212 / (13176 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566002007 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566002007 : ℝ) + 3.141593 * 0.052295246329 / (13176 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144611610 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295246329)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328819212) : PiBarMP 13176 12 0.011 xi bn ≤ 0.158282884129 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13176 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036452972609 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.153685880045 : ℝ) ≤ √((13176 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.786758818253 : ℝ) ≤ √(13176 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13176) ≤ 0.121376441031 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036452972609 + 0.052295246329 * 1.772454 / (2 * (114.153685880045 : ℝ))) * (1 + 0.001144611610) +
        8 / (13176 * 114.786758818253) + 0.121376441031 := by gcongr
    _ ≤ (0.158282884129 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295246329)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328819212) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280198914298) :
    parallelOracle 13176 0.011 xi bn cd ≤ 0.159237660741 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13176 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13176 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524316765 : ℝ) ≤ plow 13176 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.786758818253 : ℝ) ≤ √(13176 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280198914298 : ℝ) / (2 * 0.560524316765 * 114.786758818253)) * 0.158282884129 +
        0.280198914298 ^ 2 / (2 * 0.560524316765 * 114.786758818253) := by gcongr
    _ ≤ (0.159237660741 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052295246329) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328819212)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280198914298) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13176 13176 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524316765 : ℝ) ≤ plow 13176 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.786758818253 : ℝ) ≤ √(13176 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13176 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13176 Θ 1.22 ≤ 0.011552730591 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.786758818253 := by gcongr <;> linarith
      _ ≤ (0.011552730591 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13176 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13176 13176 0.011 ≤ 0.008327501414 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13176 13176 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13176 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13176 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13176 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13176 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159237660741 + 0.011552730591 + (0.008327501414 : ℝ) *
        (1 + 2 * (0.280198914298 + 0.011552730591) / (0.560524316765 * 114.786758818253))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13176]

end BstLean.Part269.N13176

/-! The original eight local profiles supply actual 13176 moment certificates. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13176 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052295246329 ∧
    0 ≤ bN 13176 BstLean.Part154.csC (groupTheta g) ∧ bN 13176 BstLean.Part154.csC (groupTheta g) ≤ 0.001328819212 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13176 13176 0.011
      (momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13176 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13176 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13176 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228681539109 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13176 0.011
      (momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13176 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13176
/-! The actual computed-centre upper energy formula at 13176. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13176

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13176)
open BstLean.Part268 (cell13176)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084211104297
  | 2 => 0.085134105091
  | 3 => 0.086052488206
  | 4 => 0.086967021976
  | 5 => 0.087878653947
  | 6 => 0.088788539693
  | 7 => 0.089698074765
  | 8 => 0.090608929906
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13176 13176 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13176 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13176

/-! Actual upper energy certificates on all 43 source endpoints at 13176. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13176)
open BstLean.Part268 (cell13176)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13176 (gMinus 13176) (1 - (cell13176 i).lower) ≤ 1 ∧
    energyUpper 13176 (gMinus 13176) (BstLean.Part211.gPlus 13176)
      (finiteEnergy 13176 13176 0.011) (1 - (cell13176 i).lower) ≤
      (cell13176 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨10,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨11,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨12,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨13,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨14,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨15,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨16,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨17,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨18,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨19,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨20,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨21,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨22,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨23,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨24,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨25,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨26,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨27,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨28,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨29,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨30,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨31,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨32,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨33,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨34,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨35,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨36,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨37,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨38,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨39,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨40,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨41,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨42,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨43,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨44,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨45,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨46,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨47,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨48,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨49,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨50,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨51,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13176) (by norm_num)
        (q := 1 - (cell13176 ⟨52,by decide⟩).lower)
        (by norm_num [cell13176]) (by norm_num [cell13176])
      exact ⟨E.1,E.2.trans (by norm_num [cell13176])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13176

/-! Source-cell containment and simple scalar guards at 13176. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13176)
open BstLean.Part268 (cell13176)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13176 ⟨10,by decide⟩).lower ∧ (cell13176 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13176 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13176 ⟨11,by decide⟩).lower ∧ (cell13176 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13176 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13176 ⟨12,by decide⟩).lower ∧ (cell13176 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13176 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13176 ⟨13,by decide⟩).lower ∧ (cell13176 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13176 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13176 ⟨14,by decide⟩).lower ∧ (cell13176 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13176 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13176 ⟨15,by decide⟩).lower ∧ (cell13176 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13176 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13176 ⟨16,by decide⟩).lower ∧ (cell13176 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13176 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13176 ⟨17,by decide⟩).lower ∧ (cell13176 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13176 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13176 ⟨18,by decide⟩).lower ∧ (cell13176 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13176 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13176 ⟨19,by decide⟩).lower ∧ (cell13176 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13176 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13176 ⟨20,by decide⟩).lower ∧ (cell13176 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13176 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13176 ⟨21,by decide⟩).lower ∧ (cell13176 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13176 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13176 ⟨22,by decide⟩).lower ∧ (cell13176 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13176 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13176 ⟨23,by decide⟩).lower ∧ (cell13176 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13176 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13176 ⟨24,by decide⟩).lower ∧ (cell13176 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13176 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13176 ⟨25,by decide⟩).lower ∧ (cell13176 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13176 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13176 ⟨26,by decide⟩).lower ∧ (cell13176 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13176 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13176 ⟨27,by decide⟩).lower ∧ (cell13176 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13176 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13176 ⟨28,by decide⟩).lower ∧ (cell13176 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13176 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13176 ⟨29,by decide⟩).lower ∧ (cell13176 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13176 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13176 ⟨30,by decide⟩).lower ∧ (cell13176 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13176 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13176 ⟨31,by decide⟩).lower ∧ (cell13176 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13176 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13176 ⟨32,by decide⟩).lower ∧ (cell13176 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13176 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13176 ⟨33,by decide⟩).lower ∧ (cell13176 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13176 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13176 ⟨34,by decide⟩).lower ∧ (cell13176 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13176 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13176 ⟨35,by decide⟩).lower ∧ (cell13176 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13176 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13176 ⟨36,by decide⟩).lower ∧ (cell13176 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13176 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13176 ⟨37,by decide⟩).lower ∧ (cell13176 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13176 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13176 ⟨38,by decide⟩).lower ∧ (cell13176 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13176 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13176 ⟨39,by decide⟩).lower ∧ (cell13176 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13176 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13176 ⟨40,by decide⟩).lower ∧ (cell13176 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13176 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13176 ⟨41,by decide⟩).lower ∧ (cell13176 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13176 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13176 ⟨42,by decide⟩).lower ∧ (cell13176 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13176 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13176 ⟨43,by decide⟩).lower ∧ (cell13176 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13176 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13176 ⟨44,by decide⟩).lower ∧ (cell13176 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13176 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13176 ⟨45,by decide⟩).lower ∧ (cell13176 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13176 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13176 ⟨46,by decide⟩).lower ∧ (cell13176 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13176 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13176 ⟨47,by decide⟩).lower ∧ (cell13176 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13176 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13176 ⟨48,by decide⟩).lower ∧ (cell13176 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13176 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13176 ⟨49,by decide⟩).lower ∧ (cell13176 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13176 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13176 ⟨50,by decide⟩).lower ∧ (cell13176 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13176 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13176 ⟨51,by decide⟩).lower ∧ (cell13176 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13176 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13176 ⟨52,by decide⟩).lower ∧ (cell13176 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13176 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13176 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13176 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13176,cell13176,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13176 i).lower ∧
    (cell13176 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13176 i).upper ≤ (0.532 : ℝ) ∧
    (cell13176 i).centre ≤ (0.1 : ℝ) ∧ (cell13176 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13176 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13176 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13176

/-! The local source numeric instances at 13176 have no network premises. -/
namespace BstLean.Part269.N13176
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13176)
open BstLean.Part268 (cell13176)

noncomputable def sourceNumerics13176 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13176 (cell13176 i)
      scalarRow13176.M scalarRow13176.H scalarRow13176.xi := by
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
    energy_allowance := scalarRow13176.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13176]
    centre_nonneg := (scalarRow13176.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13176])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13176
/-! Actual 13177 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13177 ≤ (1.035149461832 : ℝ) := by
  have hr : (114.791114638721 : ℝ) ≤ √(13177 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.791114638721 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13177 13177 (11 / 1000) ≤
    (0.008327185419 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13177) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.791114638721 : ℝ) ≤ √(13177 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13177)
  have hdiv : K / √(13177 : ℝ) ≤ K / 114.791114638721 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.791114638721 ≤ (0.008327185419 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13177.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13177 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13177 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13177 := gPlus_lower 13177
end BstLean.Part269.N13177

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13177
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035149461831 : ℝ) ≤ wn 13177 := by
  have hn : √(13177 : ℝ) ≤ 114.791114638722 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13177 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.791114638722 ≤ 2 / √(13177 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242608295 : ℝ) ≤ rhoBar 13177 BstLean.Part154.csC ∧
    rhoBar 13177 BstLean.Part154.csC ≤ 0.000242608671 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035149461831 : ℝ) / (1.295212 * 13177) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035149461832 : ℝ) / (1.29521 * 13177) := by gcongr
      _ ≤ (0.000242608671 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13177 BstLean.Part154.csC) ≤ 0.000970493543 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13177 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) ≤ 0.000185305822 ∧
    cc1 (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) ≤ 0.000117911390 ∧
    cc2 (rhoBar 13177 BstLean.Part154.csC) ≤ 0.000068448545 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13177 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13177 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13177 BstLean.Part154.csC * nuR (rhoBar 13177 BstLean.Part154.csC)) ≤ 0.000485232057 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242608671 : ℝ) * 0.000970493543 := by gcongr
      _ ≤ (0.000485232057 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13177 BstLean.Part154.csC) * nuR (rhoBar 13177 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970493543 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13177 BstLean.Part154.csC) * rhoBar 13177 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242608671 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242608671 / 2 + 0.399 * 0.000970493543 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185305822 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485232057 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117911390 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242608671 / 1.414213562 := by gcongr
      _ ≤ (0.000068448545 : ℝ) := by norm_num

end BstLean.Part269.N13177

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13177
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) ≤ 1.48291E-7 := by
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13177 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13177 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13177 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185305822 : ℝ) ^ 2 + 0.000117911390 ^ 2 + 3 * 0.000068448545 ^ 2 +
        2 * 0.797885 * 0.000185305822 * 0.000117911390 + 2 * 0.000185305822 * 0.000068448545 +
        4 * 0.797885 * 0.000117911390 * 0.000068448545 := by gcongr
    _ ≤ (1.48291E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13177 BstLean.Part154.csC Θ ≤ 0.002530883767 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13177 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13177 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13177 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035149461832 * 1.48291E-7 / (0.000242608295 : ℝ) := by gcongr
    _ ≤ 0.002530883767 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13177 BstLean.Part154.csC Θ ≤ 0.002806356136 + 0.000639513305 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13177 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13177 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035149461832 : ℝ) * ((2 * Θ * 0.000242608671 +
        (6863 / 10000) * 0.000242608671 * 13177 * 0.000970493543) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002806356136 + 0.000639513305 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13177 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13177 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13177 0.011 Θ ∧ gammaRatio 13177 0.011 Θ ≤ 0.000083402588 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13177 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035149461832 : ℝ) * 0.525 / ((1 - 0.011) * 13177) := by gcongr
      _ ≤ (0.000083402588 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13177 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13177 0.011 Θ) :=
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
    badAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13177 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13177 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13177 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13177 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13177 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13177 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13177 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13177 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13177 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13177 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035149461832 : ℝ) * 13177 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003123832336 + 0.003170397072 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13177

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13177
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13177 BstLean.Part154.csC) (piBar (rhoBar 13177 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13177 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13177 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13177 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13177 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13177 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13177 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13177 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13177 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13177 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13177 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051515399515 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13177) ≤ 0.010403571608 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13177 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035149461832)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010403571608 + 2 * 0.737676 / 13177) := by gcongr
    _ ≤ (0.051515399515 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13177 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13177

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13177
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524358776 : ℝ) ≤ plow 13177 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13177) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294890799)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328713978) : eMP 13177 0.011 xi bn ≤ 0.001144522789 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13177 : ℝ) * (1 - 0.011))) ≤ 0.000565958118 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328713978 / (13177 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565958118 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565958118 : ℝ) + 3.141593 * 0.052294890799 / (13177 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144522789 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294890799)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328713978) : PiBarMP 13177 12 0.011 xi bn ≤ 0.158276811259 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13177 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036451529159 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.158017677252 : ℝ) ≤ √((13177 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.791114638721 : ℝ) ≤ √(13177 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13177) ≤ 0.121371835326 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036451529159 + 0.052294890799 * 1.772454 / (2 * (114.158017677252 : ℝ))) * (1 + 0.001144522789) +
        8 / (13177 * 114.791114638721) + 0.121371835326 := by gcongr
    _ ≤ (0.158276811259 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294890799)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328713978) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280196161275) :
    parallelOracle 13177 0.011 xi bn cd ≤ 0.159231522972 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13177 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13177 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524358776 : ℝ) ≤ plow 13177 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.791114638721 : ℝ) ≤ √(13177 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280196161275 : ℝ) / (2 * 0.560524358776 * 114.791114638721)) * 0.158276811259 +
        0.280196161275 ^ 2 / (2 * 0.560524358776 * 114.791114638721) := by gcongr
    _ ≤ (0.159231522972 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294890799) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328713978)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280196161275) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13177 13177 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524358776 : ℝ) ≤ plow 13177 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.791114638721 : ℝ) ≤ √(13177 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13177 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13177 Θ 1.22 ≤ 0.011552292216 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.791114638721 := by gcongr <;> linarith
      _ ≤ (0.011552292216 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13177 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13177 13177 0.011 ≤ 0.008327185419 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13177 13177 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13177 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13177 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13177 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13177 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159231522972 + 0.011552292216 + (0.008327185419 : ℝ) *
        (1 + 2 * (0.280196161275 + 0.011552292216) / (0.560524358776 * 114.791114638721))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13177]

end BstLean.Part269.N13177

/-! The original eight local profiles supply actual 13177 moment certificates. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13177 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052294890799 ∧
    0 ≤ bN 13177 BstLean.Part154.csC (groupTheta g) ∧ bN 13177 BstLean.Part154.csC (groupTheta g) ≤ 0.001328713978 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13177 13177 0.011
      (momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13177 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13177 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13177 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228680761760 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13177 0.011
      (momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13177 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13177
/-! The actual computed-centre upper energy formula at 13177. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13177

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13177)
open BstLean.Part268 (cell13177)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084208617413
  | 2 => 0.085131588149
  | 3 => 0.086049937035
  | 4 => 0.086964431401
  | 5 => 0.087876017601
  | 6 => 0.088785849804
  | 7 => 0.089695321917
  | 8 => 0.090606102767
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13177 13177 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13177 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13177

/-! Actual upper energy certificates on all 43 source endpoints at 13177. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13177)
open BstLean.Part268 (cell13177)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13177 (gMinus 13177) (1 - (cell13177 i).lower) ≤ 1 ∧
    energyUpper 13177 (gMinus 13177) (BstLean.Part211.gPlus 13177)
      (finiteEnergy 13177 13177 0.011) (1 - (cell13177 i).lower) ≤
      (cell13177 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨10,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨11,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨12,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨13,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨14,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨15,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨16,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨17,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨18,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨19,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨20,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨21,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨22,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨23,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨24,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨25,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨26,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨27,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨28,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨29,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨30,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨31,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨32,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨33,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨34,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨35,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨36,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨37,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨38,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨39,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨40,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨41,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨42,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨43,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨44,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨45,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨46,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨47,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨48,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨49,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨50,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨51,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13177) (by norm_num)
        (q := 1 - (cell13177 ⟨52,by decide⟩).lower)
        (by norm_num [cell13177]) (by norm_num [cell13177])
      exact ⟨E.1,E.2.trans (by norm_num [cell13177])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13177

/-! Source-cell containment and simple scalar guards at 13177. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13177)
open BstLean.Part268 (cell13177)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13177 ⟨10,by decide⟩).lower ∧ (cell13177 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13177 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13177 ⟨11,by decide⟩).lower ∧ (cell13177 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13177 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13177 ⟨12,by decide⟩).lower ∧ (cell13177 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13177 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13177 ⟨13,by decide⟩).lower ∧ (cell13177 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13177 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13177 ⟨14,by decide⟩).lower ∧ (cell13177 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13177 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13177 ⟨15,by decide⟩).lower ∧ (cell13177 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13177 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13177 ⟨16,by decide⟩).lower ∧ (cell13177 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13177 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13177 ⟨17,by decide⟩).lower ∧ (cell13177 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13177 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13177 ⟨18,by decide⟩).lower ∧ (cell13177 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13177 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13177 ⟨19,by decide⟩).lower ∧ (cell13177 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13177 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13177 ⟨20,by decide⟩).lower ∧ (cell13177 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13177 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13177 ⟨21,by decide⟩).lower ∧ (cell13177 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13177 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13177 ⟨22,by decide⟩).lower ∧ (cell13177 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13177 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13177 ⟨23,by decide⟩).lower ∧ (cell13177 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13177 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13177 ⟨24,by decide⟩).lower ∧ (cell13177 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13177 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13177 ⟨25,by decide⟩).lower ∧ (cell13177 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13177 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13177 ⟨26,by decide⟩).lower ∧ (cell13177 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13177 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13177 ⟨27,by decide⟩).lower ∧ (cell13177 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13177 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13177 ⟨28,by decide⟩).lower ∧ (cell13177 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13177 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13177 ⟨29,by decide⟩).lower ∧ (cell13177 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13177 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13177 ⟨30,by decide⟩).lower ∧ (cell13177 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13177 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13177 ⟨31,by decide⟩).lower ∧ (cell13177 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13177 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13177 ⟨32,by decide⟩).lower ∧ (cell13177 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13177 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13177 ⟨33,by decide⟩).lower ∧ (cell13177 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13177 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13177 ⟨34,by decide⟩).lower ∧ (cell13177 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13177 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13177 ⟨35,by decide⟩).lower ∧ (cell13177 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13177 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13177 ⟨36,by decide⟩).lower ∧ (cell13177 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13177 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13177 ⟨37,by decide⟩).lower ∧ (cell13177 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13177 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13177 ⟨38,by decide⟩).lower ∧ (cell13177 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13177 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13177 ⟨39,by decide⟩).lower ∧ (cell13177 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13177 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13177 ⟨40,by decide⟩).lower ∧ (cell13177 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13177 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13177 ⟨41,by decide⟩).lower ∧ (cell13177 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13177 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13177 ⟨42,by decide⟩).lower ∧ (cell13177 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13177 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13177 ⟨43,by decide⟩).lower ∧ (cell13177 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13177 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13177 ⟨44,by decide⟩).lower ∧ (cell13177 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13177 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13177 ⟨45,by decide⟩).lower ∧ (cell13177 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13177 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13177 ⟨46,by decide⟩).lower ∧ (cell13177 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13177 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13177 ⟨47,by decide⟩).lower ∧ (cell13177 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13177 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13177 ⟨48,by decide⟩).lower ∧ (cell13177 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13177 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13177 ⟨49,by decide⟩).lower ∧ (cell13177 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13177 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13177 ⟨50,by decide⟩).lower ∧ (cell13177 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13177 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13177 ⟨51,by decide⟩).lower ∧ (cell13177 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13177 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13177 ⟨52,by decide⟩).lower ∧ (cell13177 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13177 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13177 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13177 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13177,cell13177,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13177 i).lower ∧
    (cell13177 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13177 i).upper ≤ (0.532 : ℝ) ∧
    (cell13177 i).centre ≤ (0.1 : ℝ) ∧ (cell13177 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13177 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13177 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13177

/-! The local source numeric instances at 13177 have no network premises. -/
namespace BstLean.Part269.N13177
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13177)
open BstLean.Part268 (cell13177)

noncomputable def sourceNumerics13177 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13177 (cell13177 i)
      scalarRow13177.M scalarRow13177.H scalarRow13177.xi := by
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
    energy_allowance := scalarRow13177.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13177]
    centre_nonneg := (scalarRow13177.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13177])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13177
/-! Actual 13178 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13178 ≤ (1.035148116648 : ℝ) := by
  have hr : (114.795470293910 : ℝ) ≤ √(13178 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.795470293910 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13178 13178 (11 / 1000) ≤
    (0.008326869461 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13178) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.795470293910 : ℝ) ≤ √(13178 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13178)
  have hdiv : K / √(13178 : ℝ) ≤ K / 114.795470293910 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.795470293910 ≤ (0.008326869461 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13178.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13178 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13178 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13178 := gPlus_lower 13178
end BstLean.Part269.N13178

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13178
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035148116647 : ℝ) ≤ wn 13178 := by
  have hn : √(13178 : ℝ) ≤ 114.795470293911 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13178 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.795470293911 ≤ 2 / √(13178 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242589570 : ℝ) ≤ rhoBar 13178 BstLean.Part154.csC ∧
    rhoBar 13178 BstLean.Part154.csC ≤ 0.000242589945 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035148116647 : ℝ) / (1.295212 * 13178) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035148116648 : ℝ) / (1.29521 * 13178) := by gcongr
      _ ≤ (0.000242589945 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13178 BstLean.Part154.csC) ≤ 0.000970418630 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13178 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) ≤ 0.000185291519 ∧
    cc1 (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) ≤ 0.000117902289 ∧
    cc2 (rhoBar 13178 BstLean.Part154.csC) ≤ 0.000068443262 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13178 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13178 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13178 BstLean.Part154.csC * nuR (rhoBar 13178 BstLean.Part154.csC)) ≤ 0.000485194603 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242589945 : ℝ) * 0.000970418630 := by gcongr
      _ ≤ (0.000485194603 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13178 BstLean.Part154.csC) * nuR (rhoBar 13178 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970418630 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13178 BstLean.Part154.csC) * rhoBar 13178 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242589945 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242589945 / 2 + 0.399 * 0.000970418630 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185291519 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485194603 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117902289 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242589945 / 1.414213562 := by gcongr
      _ ≤ (0.000068443262 : ℝ) := by norm_num

end BstLean.Part269.N13178

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13178
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) ≤ 1.48268E-7 := by
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13178 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13178 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13178 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185291519 : ℝ) ^ 2 + 0.000117902289 ^ 2 + 3 * 0.000068443262 ^ 2 +
        2 * 0.797885 * 0.000185291519 * 0.000117902289 + 2 * 0.000185291519 * 0.000068443262 +
        4 * 0.797885 * 0.000117902289 * 0.000068443262 := by gcongr
    _ ≤ (1.48268E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13178 BstLean.Part154.csC Θ ≤ 0.002530683260 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13178 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13178 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13178 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035148116648 * 1.48268E-7 / (0.000242589570 : ℝ) := by gcongr
    _ ≤ 0.002530683260 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13178 BstLean.Part154.csC Θ ≤ 0.002806132211 + 0.000639463113 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13178 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13178 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035148116648 : ℝ) * ((2 * Θ * 0.000242589945 +
        (6863 / 10000) * 0.000242589945 * 13178 * 0.000970418630) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002806132211 + 0.000639463113 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13178 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13178 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13178 0.011 Θ ∧ gammaRatio 13178 0.011 Θ ≤ 0.000083396150 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13178 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035148116648 : ℝ) * 0.525 / ((1 - 0.011) * 13178) := by gcongr
      _ ≤ (0.000083396150 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13178 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13178 0.011 Θ) :=
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
    badAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13178 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13178 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13178 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13178 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13178 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13178 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13178 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13178 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13178 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13178 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035148116648 : ℝ) * 13178 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003123608411 + 0.003170146373 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13178

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13178
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13178 BstLean.Part154.csC) (piBar (rhoBar 13178 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13178 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13178 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13178 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13178 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13178 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13178 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13178 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13178 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13178 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13178 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051513424069 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13178) ≤ 0.010403176868 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13178 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035148116648)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010403176868 + 2 * 0.737676 / 13178) := by gcongr
    _ ≤ (0.051513424069 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13178 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13178

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13178
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524400781 : ℝ) ≤ plow 13178 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13178) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294535257)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328608712) : eMP 13178 0.011 xi bn ≤ 0.001144433963 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13178 : ℝ) * (1 - 0.011))) ≤ 0.000565914226 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328608712 / (13178 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565914226 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565914226 : ℝ) + 3.141593 * 0.052294535257 / (13178 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144433963 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294535257)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328608712) : PiBarMP 13178 12 0.011 xi bn ≤ 0.158270738419 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13178 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036450085213 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.162349310094 : ℝ) ≤ √((13178 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.795470293910 : ℝ) ≤ √(13178 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13178) ≤ 0.121367230145 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036450085213 + 0.052294535257 * 1.772454 / (2 * (114.162349310094 : ℝ))) * (1 + 0.001144433963) +
        8 / (13178 * 114.795470293910) + 0.121367230145 := by gcongr
    _ ≤ (0.158270738419 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294535257)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328608712) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280193408452) :
    parallelOracle 13178 0.011 xi bn cd ≤ 0.159225385241 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13178 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13178 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524400781 : ℝ) ≤ plow 13178 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.795470293910 : ℝ) ≤ √(13178 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280193408452 : ℝ) / (2 * 0.560524400781 * 114.795470293910)) * 0.158270738419 +
        0.280193408452 ^ 2 / (2 * 0.560524400781 * 114.795470293910) := by gcongr
    _ ≤ (0.159225385241 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294535257) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328608712)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280193408452) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13178 13178 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524400781 : ℝ) ≤ plow 13178 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.795470293910 : ℝ) ≤ √(13178 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13178 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13178 Θ 1.22 ≤ 0.011551853890 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.795470293910 := by gcongr <;> linarith
      _ ≤ (0.011551853890 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13178 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13178 13178 0.011 ≤ 0.008326869461 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13178 13178 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13178 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13178 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13178 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13178 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159225385241 + 0.011551853890 + (0.008326869461 : ℝ) *
        (1 + 2 * (0.280193408452 + 0.011551853890) / (0.560524400781 * 114.795470293910))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13178]

end BstLean.Part269.N13178

/-! The original eight local profiles supply actual 13178 moment certificates. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13178 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052294535257 ∧
    0 ≤ bN 13178 BstLean.Part154.csC (groupTheta g) ∧ bN 13178 BstLean.Part154.csC (groupTheta g) ≤ 0.001328608712 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13178 13178 0.011
      (momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13178 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13178 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13178 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228679984383 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13178 0.011
      (momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13178 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13178
/-! The actual computed-centre upper energy formula at 13178. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13178

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13178)
open BstLean.Part268 (cell13178)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084206131218
  | 2 => 0.085129071920
  | 3 => 0.086047386605
  | 4 => 0.086961841601
  | 5 => 0.087873382073
  | 6 => 0.088783160786
  | 7 => 0.089692570004
  | 8 => 0.090603276639
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13178 13178 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13178 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13178

/-! Actual upper energy certificates on all 43 source endpoints at 13178. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13178)
open BstLean.Part268 (cell13178)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13178 (gMinus 13178) (1 - (cell13178 i).lower) ≤ 1 ∧
    energyUpper 13178 (gMinus 13178) (BstLean.Part211.gPlus 13178)
      (finiteEnergy 13178 13178 0.011) (1 - (cell13178 i).lower) ≤
      (cell13178 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨10,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨11,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨12,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨13,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨14,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨15,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨16,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨17,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨18,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨19,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨20,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨21,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨22,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨23,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨24,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨25,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨26,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨27,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨28,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨29,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨30,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨31,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨32,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨33,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨34,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨35,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨36,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨37,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨38,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨39,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨40,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨41,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨42,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨43,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨44,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨45,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨46,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨47,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨48,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨49,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨50,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨51,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13178) (by norm_num)
        (q := 1 - (cell13178 ⟨52,by decide⟩).lower)
        (by norm_num [cell13178]) (by norm_num [cell13178])
      exact ⟨E.1,E.2.trans (by norm_num [cell13178])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13178

/-! Source-cell containment and simple scalar guards at 13178. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13178)
open BstLean.Part268 (cell13178)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13178 ⟨10,by decide⟩).lower ∧ (cell13178 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13178 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13178 ⟨11,by decide⟩).lower ∧ (cell13178 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13178 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13178 ⟨12,by decide⟩).lower ∧ (cell13178 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13178 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13178 ⟨13,by decide⟩).lower ∧ (cell13178 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13178 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13178 ⟨14,by decide⟩).lower ∧ (cell13178 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13178 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13178 ⟨15,by decide⟩).lower ∧ (cell13178 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13178 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13178 ⟨16,by decide⟩).lower ∧ (cell13178 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13178 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13178 ⟨17,by decide⟩).lower ∧ (cell13178 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13178 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13178 ⟨18,by decide⟩).lower ∧ (cell13178 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13178 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13178 ⟨19,by decide⟩).lower ∧ (cell13178 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13178 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13178 ⟨20,by decide⟩).lower ∧ (cell13178 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13178 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13178 ⟨21,by decide⟩).lower ∧ (cell13178 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13178 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13178 ⟨22,by decide⟩).lower ∧ (cell13178 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13178 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13178 ⟨23,by decide⟩).lower ∧ (cell13178 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13178 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13178 ⟨24,by decide⟩).lower ∧ (cell13178 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13178 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13178 ⟨25,by decide⟩).lower ∧ (cell13178 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13178 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13178 ⟨26,by decide⟩).lower ∧ (cell13178 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13178 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13178 ⟨27,by decide⟩).lower ∧ (cell13178 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13178 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13178 ⟨28,by decide⟩).lower ∧ (cell13178 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13178 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13178 ⟨29,by decide⟩).lower ∧ (cell13178 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13178 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13178 ⟨30,by decide⟩).lower ∧ (cell13178 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13178 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13178 ⟨31,by decide⟩).lower ∧ (cell13178 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13178 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13178 ⟨32,by decide⟩).lower ∧ (cell13178 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13178 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13178 ⟨33,by decide⟩).lower ∧ (cell13178 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13178 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13178 ⟨34,by decide⟩).lower ∧ (cell13178 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13178 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13178 ⟨35,by decide⟩).lower ∧ (cell13178 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13178 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13178 ⟨36,by decide⟩).lower ∧ (cell13178 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13178 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13178 ⟨37,by decide⟩).lower ∧ (cell13178 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13178 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13178 ⟨38,by decide⟩).lower ∧ (cell13178 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13178 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13178 ⟨39,by decide⟩).lower ∧ (cell13178 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13178 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13178 ⟨40,by decide⟩).lower ∧ (cell13178 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13178 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13178 ⟨41,by decide⟩).lower ∧ (cell13178 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13178 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13178 ⟨42,by decide⟩).lower ∧ (cell13178 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13178 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13178 ⟨43,by decide⟩).lower ∧ (cell13178 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13178 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13178 ⟨44,by decide⟩).lower ∧ (cell13178 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13178 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13178 ⟨45,by decide⟩).lower ∧ (cell13178 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13178 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13178 ⟨46,by decide⟩).lower ∧ (cell13178 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13178 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13178 ⟨47,by decide⟩).lower ∧ (cell13178 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13178 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13178 ⟨48,by decide⟩).lower ∧ (cell13178 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13178 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13178 ⟨49,by decide⟩).lower ∧ (cell13178 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13178 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13178 ⟨50,by decide⟩).lower ∧ (cell13178 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13178 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13178 ⟨51,by decide⟩).lower ∧ (cell13178 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13178 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13178 ⟨52,by decide⟩).lower ∧ (cell13178 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13178 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13178 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13178 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13178,cell13178,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13178 i).lower ∧
    (cell13178 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13178 i).upper ≤ (0.532 : ℝ) ∧
    (cell13178 i).centre ≤ (0.1 : ℝ) ∧ (cell13178 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13178 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13178 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13178

/-! The local source numeric instances at 13178 have no network premises. -/
namespace BstLean.Part269.N13178
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13178)
open BstLean.Part268 (cell13178)

noncomputable def sourceNumerics13178 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13178 (cell13178 i)
      scalarRow13178.M scalarRow13178.H scalarRow13178.xi := by
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
    energy_allowance := scalarRow13178.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13178]
    centre_nonneg := (scalarRow13178.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13178])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13178
/-! Actual 13179 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13179 ≤ (1.035146771617 : ℝ) := by
  have hr : (114.799825783839 : ℝ) ≤ √(13179 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.799825783839 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13179 13179 (11 / 1000) ≤
    (0.008326553538 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13179) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.799825783839 : ℝ) ≤ √(13179 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13179)
  have hdiv : K / √(13179 : ℝ) ≤ K / 114.799825783839 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.799825783839 ≤ (0.008326553538 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13179.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13179 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13179 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13179 := gPlus_lower 13179
end BstLean.Part269.N13179

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13179
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035146771616 : ℝ) ≤ wn 13179 := by
  have hn : √(13179 : ℝ) ≤ 114.799825783840 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13179 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.799825783840 ≤ 2 / √(13179 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242570847 : ℝ) ≤ rhoBar 13179 BstLean.Part154.csC ∧
    rhoBar 13179 BstLean.Part154.csC ≤ 0.000242571223 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035146771616 : ℝ) / (1.295212 * 13179) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035146771617 : ℝ) / (1.29521 * 13179) := by gcongr
      _ ≤ (0.000242571223 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13179 BstLean.Part154.csC) ≤ 0.000970343733 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13179 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) ≤ 0.000185277218 ∧
    cc1 (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) ≤ 0.000117893190 ∧
    cc2 (rhoBar 13179 BstLean.Part154.csC) ≤ 0.000068437979 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13179 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13179 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13179 BstLean.Part154.csC * nuR (rhoBar 13179 BstLean.Part154.csC)) ≤ 0.000485157157 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242571223 : ℝ) * 0.000970343733 := by gcongr
      _ ≤ (0.000485157157 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13179 BstLean.Part154.csC) * nuR (rhoBar 13179 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970343733 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13179 BstLean.Part154.csC) * rhoBar 13179 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242571223 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242571223 / 2 + 0.399 * 0.000970343733 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185277218 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485157157 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117893190 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242571223 / 1.414213562 := by gcongr
      _ ≤ (0.000068437979 : ℝ) := by norm_num

end BstLean.Part269.N13179

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13179
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) ≤ 1.48245E-7 := by
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13179 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13179 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13179 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185277218 : ℝ) ^ 2 + 0.000117893190 ^ 2 + 3 * 0.000068437979 ^ 2 +
        2 * 0.797885 * 0.000185277218 * 0.000117893190 + 2 * 0.000185277218 * 0.000068437979 +
        4 * 0.797885 * 0.000117893190 * 0.000068437979 := by gcongr
    _ ≤ (1.48245E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13179 BstLean.Part154.csC Θ ≤ 0.002530482704 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13179 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13179 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13179 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035146771617 * 1.48245E-7 / (0.000242570847 : ℝ) := by gcongr
    _ ≤ 0.002530482704 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13179 BstLean.Part154.csC Θ ≤ 0.002805908347 + 0.000639412931 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13179 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13179 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035146771617 : ℝ) * ((2 * Θ * 0.000242571223 +
        (6863 / 10000) * 0.000242571223 * 13179 * 0.000970343733) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002805908347 + 0.000639412931 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13179 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13179 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13179 0.011 Θ ∧ gammaRatio 13179 0.011 Θ ≤ 0.000083389714 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13179 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035146771617 : ℝ) * 0.525 / ((1 - 0.011) * 13179) := by gcongr
      _ ≤ (0.000083389714 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13179 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13179 0.011 Θ) :=
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
    badAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13179 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13179 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13179 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13179 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13179 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13179 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13179 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13179 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13179 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13179 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035146771617 : ℝ) * 13179 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003123384547 + 0.003169895635 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13179

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13179
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13179 BstLean.Part154.csC) (piBar (rhoBar 13179 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13179 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13179 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13179 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13179 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13179 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13179 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13179 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13179 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13179 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13179 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051511448849 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13179) ≤ 0.010402782173 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13179 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035146771617)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010402782173 + 2 * 0.737676 / 13179) := by gcongr
    _ ≤ (0.051511448849 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13179 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13179

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13179
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524442780 : ℝ) ≤ plow 13179 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13179) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294179756)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328503420) : eMP 13179 0.011 xi bn ≤ 0.001144345131 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13179 : ℝ) * (1 - 0.011))) ≤ 0.000565870331 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328503420 / (13179 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565870331 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565870331 : ℝ) + 3.141593 * 0.052294179756 / (13179 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144345131 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294179756)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328503420) : PiBarMP 13179 12 0.011 xi bn ≤ 0.158264665692 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13179 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036448640853 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.166680778587 : ℝ) ≤ √((13179 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.799825783839 : ℝ) ≤ √(13179 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13179) ≤ 0.121362625489 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036448640853 + 0.052294179756 * 1.772454 / (2 * (114.166680778587 : ℝ))) * (1 + 0.001144345131) +
        8 / (13179 * 114.799825783839) + 0.121362625489 := by gcongr
    _ ≤ (0.158264665692 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294179756)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328503420) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280190655941) :
    parallelOracle 13179 0.011 xi bn cd ≤ 0.159219247632 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13179 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13179 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524442780 : ℝ) ≤ plow 13179 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.799825783839 : ℝ) ≤ √(13179 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280190655941 : ℝ) / (2 * 0.560524442780 * 114.799825783839)) * 0.158264665692 +
        0.280190655941 ^ 2 / (2 * 0.560524442780 * 114.799825783839) := by gcongr
    _ ≤ (0.159219247632 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052294179756) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328503420)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280190655941) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13179 13179 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524442780 : ℝ) ≤ plow 13179 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.799825783839 : ℝ) ≤ √(13179 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13179 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13179 Θ 1.22 ≤ 0.011551415614 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.799825783839 := by gcongr <;> linarith
      _ ≤ (0.011551415614 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13179 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13179 13179 0.011 ≤ 0.008326553538 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13179 13179 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13179 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13179 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13179 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13179 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159219247632 + 0.011551415614 + (0.008326553538 : ℝ) *
        (1 + 2 * (0.280190655941 + 0.011551415614) / (0.560524442780 * 114.799825783839))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13179]

end BstLean.Part269.N13179

/-! The original eight local profiles supply actual 13179 moment certificates. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13179 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052294179756 ∧
    0 ≤ bN 13179 BstLean.Part154.csC (groupTheta g) ∧ bN 13179 BstLean.Part154.csC (groupTheta g) ≤ 0.001328503420 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13179 13179 0.011
      (momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13179 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13179 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13179 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228679207092 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13179 0.011
      (momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13179 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13179
/-! The actual computed-centre upper energy formula at 13179. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13179

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13179)
open BstLean.Part268 (cell13179)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084203645711
  | 2 => 0.085126556402
  | 3 => 0.086044836914
  | 4 => 0.086959252575
  | 5 => 0.087870747362
  | 6 => 0.088780472638
  | 7 => 0.089689819025
  | 8 => 0.090600451522
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13179 13179 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13179 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13179

/-! Actual upper energy certificates on all 43 source endpoints at 13179. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13179)
open BstLean.Part268 (cell13179)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13179 (gMinus 13179) (1 - (cell13179 i).lower) ≤ 1 ∧
    energyUpper 13179 (gMinus 13179) (BstLean.Part211.gPlus 13179)
      (finiteEnergy 13179 13179 0.011) (1 - (cell13179 i).lower) ≤
      (cell13179 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨10,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨11,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨12,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨13,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨14,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨15,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨16,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨17,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨18,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨19,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨20,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨21,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨22,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨23,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨24,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨25,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨26,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨27,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨28,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨29,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨30,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨31,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨32,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨33,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨34,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨35,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨36,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨37,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨38,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨39,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨40,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨41,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨42,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨43,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨44,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨45,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨46,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨47,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨48,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨49,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨50,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨51,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13179) (by norm_num)
        (q := 1 - (cell13179 ⟨52,by decide⟩).lower)
        (by norm_num [cell13179]) (by norm_num [cell13179])
      exact ⟨E.1,E.2.trans (by norm_num [cell13179])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13179

/-! Source-cell containment and simple scalar guards at 13179. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13179)
open BstLean.Part268 (cell13179)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13179 ⟨10,by decide⟩).lower ∧ (cell13179 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13179 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13179 ⟨11,by decide⟩).lower ∧ (cell13179 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13179 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13179 ⟨12,by decide⟩).lower ∧ (cell13179 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13179 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13179 ⟨13,by decide⟩).lower ∧ (cell13179 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13179 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13179 ⟨14,by decide⟩).lower ∧ (cell13179 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13179 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13179 ⟨15,by decide⟩).lower ∧ (cell13179 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13179 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13179 ⟨16,by decide⟩).lower ∧ (cell13179 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13179 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13179 ⟨17,by decide⟩).lower ∧ (cell13179 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13179 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13179 ⟨18,by decide⟩).lower ∧ (cell13179 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13179 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13179 ⟨19,by decide⟩).lower ∧ (cell13179 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13179 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13179 ⟨20,by decide⟩).lower ∧ (cell13179 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13179 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13179 ⟨21,by decide⟩).lower ∧ (cell13179 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13179 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13179 ⟨22,by decide⟩).lower ∧ (cell13179 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13179 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13179 ⟨23,by decide⟩).lower ∧ (cell13179 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13179 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13179 ⟨24,by decide⟩).lower ∧ (cell13179 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13179 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13179 ⟨25,by decide⟩).lower ∧ (cell13179 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13179 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13179 ⟨26,by decide⟩).lower ∧ (cell13179 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13179 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13179 ⟨27,by decide⟩).lower ∧ (cell13179 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13179 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13179 ⟨28,by decide⟩).lower ∧ (cell13179 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13179 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13179 ⟨29,by decide⟩).lower ∧ (cell13179 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13179 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13179 ⟨30,by decide⟩).lower ∧ (cell13179 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13179 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13179 ⟨31,by decide⟩).lower ∧ (cell13179 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13179 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13179 ⟨32,by decide⟩).lower ∧ (cell13179 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13179 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13179 ⟨33,by decide⟩).lower ∧ (cell13179 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13179 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13179 ⟨34,by decide⟩).lower ∧ (cell13179 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13179 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13179 ⟨35,by decide⟩).lower ∧ (cell13179 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13179 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13179 ⟨36,by decide⟩).lower ∧ (cell13179 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13179 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13179 ⟨37,by decide⟩).lower ∧ (cell13179 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13179 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13179 ⟨38,by decide⟩).lower ∧ (cell13179 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13179 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13179 ⟨39,by decide⟩).lower ∧ (cell13179 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13179 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13179 ⟨40,by decide⟩).lower ∧ (cell13179 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13179 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13179 ⟨41,by decide⟩).lower ∧ (cell13179 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13179 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13179 ⟨42,by decide⟩).lower ∧ (cell13179 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13179 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13179 ⟨43,by decide⟩).lower ∧ (cell13179 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13179 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13179 ⟨44,by decide⟩).lower ∧ (cell13179 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13179 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13179 ⟨45,by decide⟩).lower ∧ (cell13179 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13179 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13179 ⟨46,by decide⟩).lower ∧ (cell13179 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13179 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13179 ⟨47,by decide⟩).lower ∧ (cell13179 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13179 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13179 ⟨48,by decide⟩).lower ∧ (cell13179 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13179 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13179 ⟨49,by decide⟩).lower ∧ (cell13179 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13179 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13179 ⟨50,by decide⟩).lower ∧ (cell13179 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13179 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13179 ⟨51,by decide⟩).lower ∧ (cell13179 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13179 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13179 ⟨52,by decide⟩).lower ∧ (cell13179 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13179 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13179 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13179 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13179,cell13179,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13179 i).lower ∧
    (cell13179 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13179 i).upper ≤ (0.532 : ℝ) ∧
    (cell13179 i).centre ≤ (0.1 : ℝ) ∧ (cell13179 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13179 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13179 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13179

/-! The local source numeric instances at 13179 have no network premises. -/
namespace BstLean.Part269.N13179
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13179)
open BstLean.Part268 (cell13179)

noncomputable def sourceNumerics13179 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13179 (cell13179 i)
      scalarRow13179.M scalarRow13179.H scalarRow13179.xi := by
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
    energy_allowance := scalarRow13179.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13179]
    centre_nonneg := (scalarRow13179.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13179])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13179
/-! Actual 13180 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13180 ≤ (1.035145426741 : ℝ) := by
  have hr : (114.804181108529 : ℝ) ≤ √(13180 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.804181108529 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13180 13180 (11 / 1000) ≤
    (0.008326237651 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13180) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.804181108529 : ℝ) ≤ √(13180 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13180)
  have hdiv : K / √(13180 : ℝ) ≤ K / 114.804181108529 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.804181108529 ≤ (0.008326237651 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13180.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13180 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13180 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13180 := gPlus_lower 13180
end BstLean.Part269.N13180

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13180
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035145426740 : ℝ) ≤ wn 13180 := by
  have hn : √(13180 : ℝ) ≤ 114.804181108530 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13180 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.804181108530 ≤ 2 / √(13180 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242552128 : ℝ) ≤ rhoBar 13180 BstLean.Part154.csC ∧
    rhoBar 13180 BstLean.Part154.csC ≤ 0.000242552503 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035145426740 : ℝ) / (1.295212 * 13180) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035145426741 : ℝ) / (1.29521 * 13180) := by gcongr
      _ ≤ (0.000242552503 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13180 BstLean.Part154.csC) ≤ 0.000970268844 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13180 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) ≤ 0.000185262919 ∧
    cc1 (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) ≤ 0.000117884091 ∧
    cc2 (rhoBar 13180 BstLean.Part154.csC) ≤ 0.000068432698 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13180 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13180 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13180 BstLean.Part154.csC * nuR (rhoBar 13180 BstLean.Part154.csC)) ≤ 0.000485119714 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242552503 : ℝ) * 0.000970268844 := by gcongr
      _ ≤ (0.000485119714 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13180 BstLean.Part154.csC) * nuR (rhoBar 13180 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970268844 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13180 BstLean.Part154.csC) * rhoBar 13180 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242552503 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242552503 / 2 + 0.399 * 0.000970268844 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185262919 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485119714 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117884091 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242552503 / 1.414213562 := by gcongr
      _ ≤ (0.000068432698 : ℝ) := by norm_num

end BstLean.Part269.N13180

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13180
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) ≤ 1.48222E-7 := by
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13180 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13180 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13180 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185262919 : ℝ) ^ 2 + 0.000117884091 ^ 2 + 3 * 0.000068432698 ^ 2 +
        2 * 0.797885 * 0.000185262919 * 0.000117884091 + 2 * 0.000185262919 * 0.000068432698 +
        4 * 0.797885 * 0.000117884091 * 0.000068432698 := by gcongr
    _ ≤ (1.48222E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13180 BstLean.Part154.csC Θ ≤ 0.002530282076 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13180 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13180 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13180 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035145426741 * 1.48222E-7 / (0.000242552128 : ℝ) := by gcongr
    _ ≤ 0.002530282076 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13180 BstLean.Part154.csC Θ ≤ 0.002805684499 + 0.000639362755 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13180 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13180 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035145426741 : ℝ) * ((2 * Θ * 0.000242552503 +
        (6863 / 10000) * 0.000242552503 * 13180 * 0.000970268844) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002805684499 + 0.000639362755 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13180 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13180 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13180 0.011 Θ ∧ gammaRatio 13180 0.011 Θ ≤ 0.000083383279 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13180 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035145426741 : ℝ) * 0.525 / ((1 - 0.011) * 13180) := by gcongr
      _ ≤ (0.000083383279 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13180 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13180 0.011 Θ) :=
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
    badAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13180 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13180 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13180 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13180 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13180 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13180 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13180 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13180 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13180 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13180 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035145426741 : ℝ) * 13180 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003123160699 + 0.003169644831 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13180

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13180
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13180 BstLean.Part154.csC) (piBar (rhoBar 13180 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13180 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13180 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13180 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13180 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13180 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13180 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13180 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13180 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13180 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13180 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051509473856 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13180) ≤ 0.010402387523 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13180 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035145426741)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010402387523 + 2 * 0.737676 / 13180) := by gcongr
    _ ≤ (0.051509473856 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13180 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13180

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13180
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524484772 : ℝ) ≤ plow 13180 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13180) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293824236)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328398090) : eMP 13180 0.011 xi bn ≤ 0.001144256291 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13180 : ℝ) * (1 - 0.011))) ≤ 0.000565826432 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328398090 / (13180 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565826432 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565826432 : ℝ) + 3.141593 * 0.052293824236 / (13180 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144256291 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293824236)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328398090) : PiBarMP 13180 12 0.011 xi bn ≤ 0.158258592913 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13180 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036447195915 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.171012082752 : ℝ) ≤ √((13180 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.804181108529 : ℝ) ≤ √(13180 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13180) ≤ 0.121358021357 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036447195915 + 0.052293824236 * 1.772454 / (2 * (114.171012082752 : ℝ))) * (1 + 0.001144256291) +
        8 / (13180 * 114.804181108529) + 0.121358021357 := by gcongr
    _ ≤ (0.158258592913 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293824236)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328398090) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280187903613) :
    parallelOracle 13180 0.011 xi bn cd ≤ 0.159213109978 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13180 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13180 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524484772 : ℝ) ≤ plow 13180 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.804181108529 : ℝ) ≤ √(13180 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280187903613 : ℝ) / (2 * 0.560524484772 * 114.804181108529)) * 0.158258592913 +
        0.280187903613 ^ 2 / (2 * 0.560524484772 * 114.804181108529) := by gcongr
    _ ≤ (0.159213109978 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293824236) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328398090)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280187903613) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13180 13180 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524484772 : ℝ) ≤ plow 13180 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.804181108529 : ℝ) ≤ √(13180 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13180 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13180 Θ 1.22 ≤ 0.011550977388 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.804181108529 := by gcongr <;> linarith
      _ ≤ (0.011550977388 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13180 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13180 13180 0.011 ≤ 0.008326237651 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13180 13180 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13180 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13180 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13180 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13180 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159213109978 + 0.011550977388 + (0.008326237651 : ℝ) *
        (1 + 2 * (0.280187903613 + 0.011550977388) / (0.560524484772 * 114.804181108529))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13180]

end BstLean.Part269.N13180

/-! The original eight local profiles supply actual 13180 moment certificates. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13180 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052293824236 ∧
    0 ≤ bN 13180 BstLean.Part154.csC (groupTheta g) ∧ bN 13180 BstLean.Part154.csC (groupTheta g) ≤ 0.001328398090 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13180 13180 0.011
      (momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13180 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13180 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13180 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228678429757 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13180 0.011
      (momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13180 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13180
/-! The actual computed-centre upper energy formula at 13180. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13180

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13180)
open BstLean.Part268 (cell13180)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084201160893
  | 2 => 0.085124041595
  | 3 => 0.086042287962
  | 4 => 0.086956664323
  | 5 => 0.087868113468
  | 6 => 0.088777785358
  | 7 => 0.089687068977
  | 8 => 0.090597627415
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13180 13180 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13180 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13180

/-! Actual upper energy certificates on all 43 source endpoints at 13180. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13180)
open BstLean.Part268 (cell13180)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13180 (gMinus 13180) (1 - (cell13180 i).lower) ≤ 1 ∧
    energyUpper 13180 (gMinus 13180) (BstLean.Part211.gPlus 13180)
      (finiteEnergy 13180 13180 0.011) (1 - (cell13180 i).lower) ≤
      (cell13180 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨10,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨11,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨12,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨13,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨14,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨15,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨16,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨17,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨18,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨19,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨20,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨21,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨22,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨23,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨24,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨25,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨26,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨27,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨28,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨29,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨30,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨31,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨32,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨33,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨34,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨35,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨36,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨37,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨38,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨39,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨40,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨41,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨42,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨43,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨44,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨45,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨46,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨47,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨48,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨49,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨50,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨51,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13180) (by norm_num)
        (q := 1 - (cell13180 ⟨52,by decide⟩).lower)
        (by norm_num [cell13180]) (by norm_num [cell13180])
      exact ⟨E.1,E.2.trans (by norm_num [cell13180])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13180

/-! Source-cell containment and simple scalar guards at 13180. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13180)
open BstLean.Part268 (cell13180)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13180 ⟨10,by decide⟩).lower ∧ (cell13180 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13180 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13180 ⟨11,by decide⟩).lower ∧ (cell13180 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13180 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13180 ⟨12,by decide⟩).lower ∧ (cell13180 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13180 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13180 ⟨13,by decide⟩).lower ∧ (cell13180 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13180 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13180 ⟨14,by decide⟩).lower ∧ (cell13180 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13180 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13180 ⟨15,by decide⟩).lower ∧ (cell13180 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13180 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13180 ⟨16,by decide⟩).lower ∧ (cell13180 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13180 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13180 ⟨17,by decide⟩).lower ∧ (cell13180 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13180 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13180 ⟨18,by decide⟩).lower ∧ (cell13180 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13180 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13180 ⟨19,by decide⟩).lower ∧ (cell13180 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13180 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13180 ⟨20,by decide⟩).lower ∧ (cell13180 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13180 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13180 ⟨21,by decide⟩).lower ∧ (cell13180 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13180 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13180 ⟨22,by decide⟩).lower ∧ (cell13180 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13180 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13180 ⟨23,by decide⟩).lower ∧ (cell13180 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13180 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13180 ⟨24,by decide⟩).lower ∧ (cell13180 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13180 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13180 ⟨25,by decide⟩).lower ∧ (cell13180 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13180 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13180 ⟨26,by decide⟩).lower ∧ (cell13180 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13180 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13180 ⟨27,by decide⟩).lower ∧ (cell13180 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13180 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13180 ⟨28,by decide⟩).lower ∧ (cell13180 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13180 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13180 ⟨29,by decide⟩).lower ∧ (cell13180 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13180 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13180 ⟨30,by decide⟩).lower ∧ (cell13180 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13180 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13180 ⟨31,by decide⟩).lower ∧ (cell13180 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13180 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13180 ⟨32,by decide⟩).lower ∧ (cell13180 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13180 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13180 ⟨33,by decide⟩).lower ∧ (cell13180 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13180 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13180 ⟨34,by decide⟩).lower ∧ (cell13180 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13180 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13180 ⟨35,by decide⟩).lower ∧ (cell13180 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13180 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13180 ⟨36,by decide⟩).lower ∧ (cell13180 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13180 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13180 ⟨37,by decide⟩).lower ∧ (cell13180 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13180 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13180 ⟨38,by decide⟩).lower ∧ (cell13180 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13180 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13180 ⟨39,by decide⟩).lower ∧ (cell13180 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13180 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13180 ⟨40,by decide⟩).lower ∧ (cell13180 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13180 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13180 ⟨41,by decide⟩).lower ∧ (cell13180 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13180 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13180 ⟨42,by decide⟩).lower ∧ (cell13180 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13180 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13180 ⟨43,by decide⟩).lower ∧ (cell13180 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13180 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13180 ⟨44,by decide⟩).lower ∧ (cell13180 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13180 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13180 ⟨45,by decide⟩).lower ∧ (cell13180 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13180 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13180 ⟨46,by decide⟩).lower ∧ (cell13180 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13180 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13180 ⟨47,by decide⟩).lower ∧ (cell13180 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13180 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13180 ⟨48,by decide⟩).lower ∧ (cell13180 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13180 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13180 ⟨49,by decide⟩).lower ∧ (cell13180 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13180 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13180 ⟨50,by decide⟩).lower ∧ (cell13180 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13180 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13180 ⟨51,by decide⟩).lower ∧ (cell13180 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13180 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13180 ⟨52,by decide⟩).lower ∧ (cell13180 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13180 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13180 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13180 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13180,cell13180,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13180 i).lower ∧
    (cell13180 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13180 i).upper ≤ (0.532 : ℝ) ∧
    (cell13180 i).centre ≤ (0.1 : ℝ) ∧ (cell13180 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13180 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13180 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13180

/-! The local source numeric instances at 13180 have no network premises. -/
namespace BstLean.Part269.N13180
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13180)
open BstLean.Part268 (cell13180)

noncomputable def sourceNumerics13180 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13180 (cell13180 i)
      scalarRow13180.M scalarRow13180.H scalarRow13180.xi := by
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
    energy_allowance := scalarRow13180.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13180]
    centre_nonneg := (scalarRow13180.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13180])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13180
/-! Actual 13181 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13181 ≤ (1.035144082018 : ℝ) := by
  have hr : (114.808536267997 : ℝ) ≤ √(13181 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.808536267997 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13181 13181 (11 / 1000) ≤
    (0.008325921801 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13181) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.808536267997 : ℝ) ≤ √(13181 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13181)
  have hdiv : K / √(13181 : ℝ) ≤ K / 114.808536267997 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.808536267997 ≤ (0.008325921801 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13181.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13181 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13181 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13181 := gPlus_lower 13181
end BstLean.Part269.N13181

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13181
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035144082017 : ℝ) ≤ wn 13181 := by
  have hn : √(13181 : ℝ) ≤ 114.808536267998 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13181 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.808536267998 ≤ 2 / √(13181 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242533411 : ℝ) ≤ rhoBar 13181 BstLean.Part154.csC ∧
    rhoBar 13181 BstLean.Part154.csC ≤ 0.000242533786 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035144082017 : ℝ) / (1.295212 * 13181) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035144082018 : ℝ) / (1.29521 * 13181) := by gcongr
      _ ≤ (0.000242533786 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13181 BstLean.Part154.csC) ≤ 0.000970193967 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13181 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) ≤ 0.000185248622 ∧
    cc1 (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) ≤ 0.000117874994 ∧
    cc2 (rhoBar 13181 BstLean.Part154.csC) ≤ 0.000068427417 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13181 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13181 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13181 BstLean.Part154.csC * nuR (rhoBar 13181 BstLean.Part154.csC)) ≤ 0.000485082278 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242533786 : ℝ) * 0.000970193967 := by gcongr
      _ ≤ (0.000485082278 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13181 BstLean.Part154.csC) * nuR (rhoBar 13181 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970193967 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13181 BstLean.Part154.csC) * rhoBar 13181 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242533786 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242533786 / 2 + 0.399 * 0.000970193967 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185248622 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485082278 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117874994 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242533786 / 1.414213562 := by gcongr
      _ ≤ (0.000068427417 : ℝ) := by norm_num

end BstLean.Part269.N13181

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13181
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) ≤ 1.48199E-7 := by
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13181 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13181 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13181 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185248622 : ℝ) ^ 2 + 0.000117874994 ^ 2 + 3 * 0.000068427417 ^ 2 +
        2 * 0.797885 * 0.000185248622 * 0.000117874994 + 2 * 0.000185248622 * 0.000068427417 +
        4 * 0.797885 * 0.000117874994 * 0.000068427417 := by gcongr
    _ ≤ (1.48199E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13181 BstLean.Part154.csC Θ ≤ 0.002530081397 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13181 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13181 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13181 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035144082018 * 1.48199E-7 / (0.000242533411 : ℝ) := by gcongr
    _ ≤ 0.002530081397 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13181 BstLean.Part154.csC Θ ≤ 0.002805460688 + 0.000639312587 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13181 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13181 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035144082018 : ℝ) * ((2 * Θ * 0.000242533786 +
        (6863 / 10000) * 0.000242533786 * 13181 * 0.000970193967) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002805460688 + 0.000639312587 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13181 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13181 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13181 0.011 Θ ∧ gammaRatio 13181 0.011 Θ ≤ 0.000083376844 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13181 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035144082018 : ℝ) * 0.525 / ((1 - 0.011) * 13181) := by gcongr
      _ ≤ (0.000083376844 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13181 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13181 0.011 Θ) :=
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
    badAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13181 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13181 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13181 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13181 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13181 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13181 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13181 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13181 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13181 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13181 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035144082018 : ℝ) * 13181 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003122936888 + 0.003169393984 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13181

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13181
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13181 BstLean.Part154.csC) (piBar (rhoBar 13181 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13181 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13181 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13181 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13181 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13181 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13181 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13181 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13181 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13181 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13181 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051507499085 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13181) ≤ 0.010401992917 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13181 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035144082018)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010401992917 + 2 * 0.737676 / 13181) := by gcongr
    _ ≤ (0.051507499085 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13181 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13181

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13181
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524526758 : ℝ) ≤ plow 13181 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13181) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293468730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328292734) : eMP 13181 0.011 xi bn ≤ 0.001144167445 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13181 : ℝ) * (1 - 0.011))) ≤ 0.000565782530 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328292734 / (13181 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565782530 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565782530 : ℝ) + 3.141593 * 0.052293468730 / (13181 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144167445 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293468730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328292734) : PiBarMP 13181 12 0.011 xi bn ≤ 0.158252520243 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13181 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036445750562 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.175343222606 : ℝ) ≤ √((13181 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.808536267997 : ℝ) ≤ √(13181 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13181) ≤ 0.121353417748 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036445750562 + 0.052293468730 * 1.772454 / (2 * (114.175343222606 : ℝ))) * (1 + 0.001144167445) +
        8 / (13181 * 114.808536267997) + 0.121353417748 := by gcongr
    _ ≤ (0.158252520243 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293468730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328292734) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280185151535) :
    parallelOracle 13181 0.011 xi bn cd ≤ 0.159206972442 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13181 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13181 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524526758 : ℝ) ≤ plow 13181 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.808536267997 : ℝ) ≤ √(13181 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280185151535 : ℝ) / (2 * 0.560524526758 * 114.808536267997)) * 0.158252520243 +
        0.280185151535 ^ 2 / (2 * 0.560524526758 * 114.808536267997) := by gcongr
    _ ≤ (0.159206972442 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293468730) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328292734)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280185151535) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13181 13181 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524526758 : ℝ) ≤ plow 13181 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.808536267997 : ℝ) ≤ √(13181 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13181 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13181 Θ 1.22 ≤ 0.011550539212 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.808536267997 := by gcongr <;> linarith
      _ ≤ (0.011550539212 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13181 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13181 13181 0.011 ≤ 0.008325921801 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13181 13181 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13181 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13181 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13181 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13181 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159206972442 + 0.011550539212 + (0.008325921801 : ℝ) *
        (1 + 2 * (0.280185151535 + 0.011550539212) / (0.560524526758 * 114.808536267997))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13181]

end BstLean.Part269.N13181

/-! The original eight local profiles supply actual 13181 moment certificates. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13181 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052293468730 ∧
    0 ≤ bN 13181 BstLean.Part154.csC (groupTheta g) ∧ bN 13181 BstLean.Part154.csC (groupTheta g) ≤ 0.001328292734 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13181 13181 0.011
      (momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13181 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13181 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13181 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228677652450 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13181 0.011
      (momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13181 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13181
/-! The actual computed-centre upper energy formula at 13181. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13181

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13181)
open BstLean.Part268 (cell13181)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084198676762
  | 2 => 0.085121527497
  | 3 => 0.086039739748
  | 4 => 0.086954076844
  | 5 => 0.087865480389
  | 6 => 0.088775098947
  | 7 => 0.089684319862
  | 8 => 0.090594804316
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13181 13181 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13181 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13181

/-! Actual upper energy certificates on all 43 source endpoints at 13181. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13181)
open BstLean.Part268 (cell13181)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13181 (gMinus 13181) (1 - (cell13181 i).lower) ≤ 1 ∧
    energyUpper 13181 (gMinus 13181) (BstLean.Part211.gPlus 13181)
      (finiteEnergy 13181 13181 0.011) (1 - (cell13181 i).lower) ≤
      (cell13181 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨10,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨11,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨12,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨13,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨14,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨15,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨16,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨17,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨18,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨19,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨20,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨21,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨22,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨23,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨24,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨25,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨26,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨27,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨28,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨29,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨30,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨31,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨32,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨33,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨34,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨35,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨36,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨37,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨38,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨39,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨40,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨41,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨42,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨43,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨44,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨45,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨46,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨47,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨48,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨49,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨50,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨51,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13181) (by norm_num)
        (q := 1 - (cell13181 ⟨52,by decide⟩).lower)
        (by norm_num [cell13181]) (by norm_num [cell13181])
      exact ⟨E.1,E.2.trans (by norm_num [cell13181])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13181

/-! Source-cell containment and simple scalar guards at 13181. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13181)
open BstLean.Part268 (cell13181)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13181 ⟨10,by decide⟩).lower ∧ (cell13181 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13181 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13181 ⟨11,by decide⟩).lower ∧ (cell13181 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13181 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13181 ⟨12,by decide⟩).lower ∧ (cell13181 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13181 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13181 ⟨13,by decide⟩).lower ∧ (cell13181 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13181 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13181 ⟨14,by decide⟩).lower ∧ (cell13181 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13181 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13181 ⟨15,by decide⟩).lower ∧ (cell13181 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13181 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13181 ⟨16,by decide⟩).lower ∧ (cell13181 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13181 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13181 ⟨17,by decide⟩).lower ∧ (cell13181 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13181 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13181 ⟨18,by decide⟩).lower ∧ (cell13181 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13181 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13181 ⟨19,by decide⟩).lower ∧ (cell13181 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13181 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13181 ⟨20,by decide⟩).lower ∧ (cell13181 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13181 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13181 ⟨21,by decide⟩).lower ∧ (cell13181 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13181 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13181 ⟨22,by decide⟩).lower ∧ (cell13181 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13181 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13181 ⟨23,by decide⟩).lower ∧ (cell13181 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13181 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13181 ⟨24,by decide⟩).lower ∧ (cell13181 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13181 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13181 ⟨25,by decide⟩).lower ∧ (cell13181 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13181 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13181 ⟨26,by decide⟩).lower ∧ (cell13181 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13181 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13181 ⟨27,by decide⟩).lower ∧ (cell13181 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13181 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13181 ⟨28,by decide⟩).lower ∧ (cell13181 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13181 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13181 ⟨29,by decide⟩).lower ∧ (cell13181 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13181 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13181 ⟨30,by decide⟩).lower ∧ (cell13181 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13181 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13181 ⟨31,by decide⟩).lower ∧ (cell13181 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13181 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13181 ⟨32,by decide⟩).lower ∧ (cell13181 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13181 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13181 ⟨33,by decide⟩).lower ∧ (cell13181 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13181 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13181 ⟨34,by decide⟩).lower ∧ (cell13181 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13181 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13181 ⟨35,by decide⟩).lower ∧ (cell13181 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13181 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13181 ⟨36,by decide⟩).lower ∧ (cell13181 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13181 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13181 ⟨37,by decide⟩).lower ∧ (cell13181 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13181 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13181 ⟨38,by decide⟩).lower ∧ (cell13181 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13181 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13181 ⟨39,by decide⟩).lower ∧ (cell13181 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13181 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13181 ⟨40,by decide⟩).lower ∧ (cell13181 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13181 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13181 ⟨41,by decide⟩).lower ∧ (cell13181 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13181 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13181 ⟨42,by decide⟩).lower ∧ (cell13181 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13181 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13181 ⟨43,by decide⟩).lower ∧ (cell13181 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13181 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13181 ⟨44,by decide⟩).lower ∧ (cell13181 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13181 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13181 ⟨45,by decide⟩).lower ∧ (cell13181 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13181 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13181 ⟨46,by decide⟩).lower ∧ (cell13181 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13181 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13181 ⟨47,by decide⟩).lower ∧ (cell13181 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13181 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13181 ⟨48,by decide⟩).lower ∧ (cell13181 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13181 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13181 ⟨49,by decide⟩).lower ∧ (cell13181 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13181 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13181 ⟨50,by decide⟩).lower ∧ (cell13181 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13181 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13181 ⟨51,by decide⟩).lower ∧ (cell13181 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13181 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13181 ⟨52,by decide⟩).lower ∧ (cell13181 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13181 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13181 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13181 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13181,cell13181,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13181 i).lower ∧
    (cell13181 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13181 i).upper ≤ (0.532 : ℝ) ∧
    (cell13181 i).centre ≤ (0.1 : ℝ) ∧ (cell13181 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13181 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13181 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13181

/-! The local source numeric instances at 13181 have no network premises. -/
namespace BstLean.Part269.N13181
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13181)
open BstLean.Part268 (cell13181)

noncomputable def sourceNumerics13181 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13181 (cell13181 i)
      scalarRow13181.M scalarRow13181.H scalarRow13181.xi := by
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
    energy_allowance := scalarRow13181.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13181]
    centre_nonneg := (scalarRow13181.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13181])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13181
/-! Actual 13182 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13182 ≤ (1.035142737449 : ℝ) := by
  have hr : (114.812891262262 : ℝ) ≤ √(13182 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.812891262262 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13182 13182 (11 / 1000) ≤
    (0.008325605986 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13182) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.812891262262 : ℝ) ≤ √(13182 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13182)
  have hdiv : K / √(13182 : ℝ) ≤ K / 114.812891262262 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.812891262262 ≤ (0.008325605986 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13182.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13182 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13182 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13182 := gPlus_lower 13182
end BstLean.Part269.N13182

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13182
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035142737448 : ℝ) ≤ wn 13182 := by
  have hn : √(13182 : ℝ) ≤ 114.812891262263 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13182 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.812891262263 ≤ 2 / √(13182 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242514697 : ℝ) ≤ rhoBar 13182 BstLean.Part154.csC ∧
    rhoBar 13182 BstLean.Part154.csC ≤ 0.000242515073 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035142737448 : ℝ) / (1.295212 * 13182) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035142737449 : ℝ) / (1.29521 * 13182) := by gcongr
      _ ≤ (0.000242515073 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13182 BstLean.Part154.csC) ≤ 0.000970119106 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13182 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) ≤ 0.000185234328 ∧
    cc1 (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) ≤ 0.000117865899 ∧
    cc2 (rhoBar 13182 BstLean.Part154.csC) ≤ 0.000068422138 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13182 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13182 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13182 BstLean.Part154.csC * nuR (rhoBar 13182 BstLean.Part154.csC)) ≤ 0.000485044850 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242515073 : ℝ) * 0.000970119106 := by gcongr
      _ ≤ (0.000485044850 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13182 BstLean.Part154.csC) * nuR (rhoBar 13182 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970119106 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13182 BstLean.Part154.csC) * rhoBar 13182 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242515073 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242515073 / 2 + 0.399 * 0.000970119106 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185234328 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485044850 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117865899 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242515073 / 1.414213562 := by gcongr
      _ ≤ (0.000068422138 : ℝ) := by norm_num

end BstLean.Part269.N13182

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13182
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) ≤ 1.48176E-7 := by
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13182 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13182 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13182 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185234328 : ℝ) ^ 2 + 0.000117865899 ^ 2 + 3 * 0.000068422138 ^ 2 +
        2 * 0.797885 * 0.000185234328 * 0.000117865899 + 2 * 0.000185234328 * 0.000068422138 +
        4 * 0.797885 * 0.000117865899 * 0.000068422138 := by gcongr
    _ ≤ (1.48176E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13182 BstLean.Part154.csC Θ ≤ 0.002529880658 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13182 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13182 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13182 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035142737449 * 1.48176E-7 / (0.000242514697 : ℝ) := by gcongr
    _ ≤ 0.002529880658 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13182 BstLean.Part154.csC Θ ≤ 0.002805236939 + 0.000639262429 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13182 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13182 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035142737449 : ℝ) * ((2 * Θ * 0.000242515073 +
        (6863 / 10000) * 0.000242515073 * 13182 * 0.000970119106) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002805236939 + 0.000639262429 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13182 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13182 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13182 0.011 Θ ∧ gammaRatio 13182 0.011 Θ ≤ 0.000083370411 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13182 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035142737449 : ℝ) * 0.525 / ((1 - 0.011) * 13182) := by gcongr
      _ ≤ (0.000083370411 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13182 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13182 0.011 Θ) :=
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
    badAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13182 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13182 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13182 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13182 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13182 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13182 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13182 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13182 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13182 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13182 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035142737449 : ℝ) * 13182 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003122713139 + 0.003169143087 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13182

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13182
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13182 BstLean.Part154.csC) (piBar (rhoBar 13182 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13182 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13182 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13182 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13182 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13182 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13182 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13182 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13182 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13182 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13182 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051505524545 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13182) ≤ 0.010401598357 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13182 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035142737449)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010401598357 + 2 * 0.737676 / 13182) := by gcongr
    _ ≤ (0.051505524545 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13182 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13182

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13182
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524568737 : ℝ) ≤ plow 13182 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13182) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293113260)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328187346) : eMP 13182 0.011 xi bn ≤ 0.001144078593 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13182 : ℝ) * (1 - 0.011))) ≤ 0.000565738625 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328187346 / (13182 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565738625 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565738625 : ℝ) + 3.141593 * 0.052293113260 / (13182 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001144078593 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293113260)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328187346) : PiBarMP 13182 12 0.011 xi bn ≤ 0.158246447603 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13182 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036444304713 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.179674198168 : ℝ) ≤ √((13182 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.812891262262 : ℝ) ≤ √(13182 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13182) ≤ 0.121348814664 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036444304713 + 0.052293113260 * 1.772454 / (2 * (114.179674198168 : ℝ))) * (1 + 0.001144078593) +
        8 / (13182 * 114.812891262262) + 0.121348814664 := by gcongr
    _ ≤ (0.158246447603 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293113260)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328187346) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280182399765) :
    parallelOracle 13182 0.011 xi bn cd ≤ 0.159200834944 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13182 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13182 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524568737 : ℝ) ≤ plow 13182 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.812891262262 : ℝ) ≤ √(13182 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280182399765 : ℝ) / (2 * 0.560524568737 * 114.812891262262)) * 0.158246447603 +
        0.280182399765 ^ 2 / (2 * 0.560524568737 * 114.812891262262) := by gcongr
    _ ≤ (0.159200834944 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052293113260) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328187346)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280182399765) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13182 13182 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524568737 : ℝ) ≤ plow 13182 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.812891262262 : ℝ) ≤ √(13182 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13182 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13182 Θ 1.22 ≤ 0.011550101086 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.812891262262 := by gcongr <;> linarith
      _ ≤ (0.011550101086 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13182 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13182 13182 0.011 ≤ 0.008325605986 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13182 13182 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13182 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13182 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13182 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13182 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159200834944 + 0.011550101086 + (0.008325605986 : ℝ) *
        (1 + 2 * (0.280182399765 + 0.011550101086) / (0.560524568737 * 114.812891262262))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13182]

end BstLean.Part269.N13182

/-! The original eight local profiles supply actual 13182 moment certificates. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13182 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052293113260 ∧
    0 ≤ bN 13182 BstLean.Part154.csC (groupTheta g) ∧ bN 13182 BstLean.Part154.csC (groupTheta g) ≤ 0.001328187346 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13182 13182 0.011
      (momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13182 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13182 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13182 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228676875220 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13182 0.011
      (momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13182 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13182
/-! The actual computed-centre upper energy formula at 13182. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13182

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13182)
open BstLean.Part268 (cell13182)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084196193318
  | 2 => 0.085119014110
  | 3 => 0.086037192272
  | 4 => 0.086951490137
  | 5 => 0.087862848125
  | 6 => 0.088772413402
  | 7 => 0.089681571677
  | 8 => 0.090591982225
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13182 13182 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13182 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13182

/-! Actual upper energy certificates on all 43 source endpoints at 13182. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13182)
open BstLean.Part268 (cell13182)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13182 (gMinus 13182) (1 - (cell13182 i).lower) ≤ 1 ∧
    energyUpper 13182 (gMinus 13182) (BstLean.Part211.gPlus 13182)
      (finiteEnergy 13182 13182 0.011) (1 - (cell13182 i).lower) ≤
      (cell13182 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨10,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨11,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨12,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨13,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨14,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨15,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨16,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨17,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨18,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨19,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨20,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨21,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨22,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨23,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨24,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨25,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨26,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨27,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨28,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨29,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨30,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨31,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨32,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨33,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨34,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨35,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨36,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨37,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨38,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨39,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨40,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨41,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨42,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨43,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨44,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨45,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨46,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨47,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨48,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨49,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨50,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨51,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13182) (by norm_num)
        (q := 1 - (cell13182 ⟨52,by decide⟩).lower)
        (by norm_num [cell13182]) (by norm_num [cell13182])
      exact ⟨E.1,E.2.trans (by norm_num [cell13182])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13182

/-! Source-cell containment and simple scalar guards at 13182. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13182)
open BstLean.Part268 (cell13182)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13182 ⟨10,by decide⟩).lower ∧ (cell13182 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13182 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13182 ⟨11,by decide⟩).lower ∧ (cell13182 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13182 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13182 ⟨12,by decide⟩).lower ∧ (cell13182 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13182 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13182 ⟨13,by decide⟩).lower ∧ (cell13182 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13182 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13182 ⟨14,by decide⟩).lower ∧ (cell13182 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13182 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13182 ⟨15,by decide⟩).lower ∧ (cell13182 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13182 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13182 ⟨16,by decide⟩).lower ∧ (cell13182 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13182 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13182 ⟨17,by decide⟩).lower ∧ (cell13182 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13182 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13182 ⟨18,by decide⟩).lower ∧ (cell13182 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13182 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13182 ⟨19,by decide⟩).lower ∧ (cell13182 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13182 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13182 ⟨20,by decide⟩).lower ∧ (cell13182 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13182 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13182 ⟨21,by decide⟩).lower ∧ (cell13182 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13182 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13182 ⟨22,by decide⟩).lower ∧ (cell13182 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13182 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13182 ⟨23,by decide⟩).lower ∧ (cell13182 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13182 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13182 ⟨24,by decide⟩).lower ∧ (cell13182 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13182 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13182 ⟨25,by decide⟩).lower ∧ (cell13182 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13182 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13182 ⟨26,by decide⟩).lower ∧ (cell13182 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13182 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13182 ⟨27,by decide⟩).lower ∧ (cell13182 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13182 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13182 ⟨28,by decide⟩).lower ∧ (cell13182 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13182 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13182 ⟨29,by decide⟩).lower ∧ (cell13182 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13182 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13182 ⟨30,by decide⟩).lower ∧ (cell13182 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13182 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13182 ⟨31,by decide⟩).lower ∧ (cell13182 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13182 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13182 ⟨32,by decide⟩).lower ∧ (cell13182 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13182 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13182 ⟨33,by decide⟩).lower ∧ (cell13182 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13182 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13182 ⟨34,by decide⟩).lower ∧ (cell13182 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13182 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13182 ⟨35,by decide⟩).lower ∧ (cell13182 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13182 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13182 ⟨36,by decide⟩).lower ∧ (cell13182 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13182 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13182 ⟨37,by decide⟩).lower ∧ (cell13182 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13182 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13182 ⟨38,by decide⟩).lower ∧ (cell13182 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13182 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13182 ⟨39,by decide⟩).lower ∧ (cell13182 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13182 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13182 ⟨40,by decide⟩).lower ∧ (cell13182 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13182 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13182 ⟨41,by decide⟩).lower ∧ (cell13182 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13182 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13182 ⟨42,by decide⟩).lower ∧ (cell13182 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13182 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13182 ⟨43,by decide⟩).lower ∧ (cell13182 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13182 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13182 ⟨44,by decide⟩).lower ∧ (cell13182 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13182 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13182 ⟨45,by decide⟩).lower ∧ (cell13182 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13182 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13182 ⟨46,by decide⟩).lower ∧ (cell13182 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13182 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13182 ⟨47,by decide⟩).lower ∧ (cell13182 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13182 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13182 ⟨48,by decide⟩).lower ∧ (cell13182 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13182 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13182 ⟨49,by decide⟩).lower ∧ (cell13182 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13182 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13182 ⟨50,by decide⟩).lower ∧ (cell13182 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13182 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13182 ⟨51,by decide⟩).lower ∧ (cell13182 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13182 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13182 ⟨52,by decide⟩).lower ∧ (cell13182 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13182 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13182 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13182 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13182,cell13182,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13182 i).lower ∧
    (cell13182 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13182 i).upper ≤ (0.532 : ℝ) ∧
    (cell13182 i).centre ≤ (0.1 : ℝ) ∧ (cell13182 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13182 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13182 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13182

/-! The local source numeric instances at 13182 have no network premises. -/
namespace BstLean.Part269.N13182
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13182)
open BstLean.Part268 (cell13182)

noncomputable def sourceNumerics13182 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13182 (cell13182 i)
      scalarRow13182.M scalarRow13182.H scalarRow13182.xi := by
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
    energy_allowance := scalarRow13182.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13182]
    centre_nonneg := (scalarRow13182.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13182])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13182
/-! Actual 13183 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13183 ≤ (1.035141393034 : ℝ) := by
  have hr : (114.817246091342 : ℝ) ≤ √(13183 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.817246091342 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13183 13183 (11 / 1000) ≤
    (0.008325290207 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13183) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.817246091342 : ℝ) ≤ √(13183 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13183)
  have hdiv : K / √(13183 : ℝ) ≤ K / 114.817246091342 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.817246091342 ≤ (0.008325290207 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13183.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13183 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13183 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13183 := gPlus_lower 13183
end BstLean.Part269.N13183

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13183
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035141393033 : ℝ) ≤ wn 13183 := by
  have hn : √(13183 : ℝ) ≤ 114.817246091343 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13183 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.817246091343 ≤ 2 / √(13183 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242495986 : ℝ) ≤ rhoBar 13183 BstLean.Part154.csC ∧
    rhoBar 13183 BstLean.Part154.csC ≤ 0.000242496362 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035141393033 : ℝ) / (1.295212 * 13183) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035141393034 : ℝ) / (1.29521 * 13183) := by gcongr
      _ ≤ (0.000242496362 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13183 BstLean.Part154.csC) ≤ 0.000970044253 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13183 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) ≤ 0.000185220036 ∧
    cc1 (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) ≤ 0.000117856805 ∧
    cc2 (rhoBar 13183 BstLean.Part154.csC) ≤ 0.000068416858 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13183 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13183 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13183 BstLean.Part154.csC * nuR (rhoBar 13183 BstLean.Part154.csC)) ≤ 0.000485007426 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242496362 : ℝ) * 0.000970044253 := by gcongr
      _ ≤ (0.000485007426 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13183 BstLean.Part154.csC) * nuR (rhoBar 13183 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000970044253 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13183 BstLean.Part154.csC) * rhoBar 13183 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242496362 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242496362 / 2 + 0.399 * 0.000970044253 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185220036 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485007426 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117856805 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242496362 / 1.414213562 := by gcongr
      _ ≤ (0.000068416858 : ℝ) := by norm_num

end BstLean.Part269.N13183

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13183
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) ≤ 1.48154E-7 := by
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13183 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13183 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13183 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185220036 : ℝ) ^ 2 + 0.000117856805 ^ 2 + 3 * 0.000068416858 ^ 2 +
        2 * 0.797885 * 0.000185220036 * 0.000117856805 + 2 * 0.000185220036 * 0.000068416858 +
        4 * 0.797885 * 0.000117856805 * 0.000068416858 := by gcongr
    _ ≤ (1.48154E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13183 BstLean.Part154.csC Θ ≤ 0.002529696932 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13183 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13183 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13183 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035141393034 * 1.48154E-7 / (0.000242495986 : ℝ) := by gcongr
    _ ≤ 0.002529696932 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13183 BstLean.Part154.csC Θ ≤ 0.002805013205 + 0.000639212278 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13183 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13183 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035141393034 : ℝ) * ((2 * Θ * 0.000242496362 +
        (6863 / 10000) * 0.000242496362 * 13183 * 0.000970044253) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002805013205 + 0.000639212278 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13183 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13183 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13183 0.011 Θ ∧ gammaRatio 13183 0.011 Θ ≤ 0.000083363979 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13183 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035141393034 : ℝ) * 0.525 / ((1 - 0.011) * 13183) := by gcongr
      _ ≤ (0.000083363979 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13183 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13183 0.011 Θ) :=
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
    badAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13183 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13183 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13183 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13183 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13183 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13183 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13183 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13183 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13183 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13183 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035141393034 : ℝ) * 13183 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003122489405 + 0.003168909210 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13183

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13183
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13183 BstLean.Part154.csC) (piBar (rhoBar 13183 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13183 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13183 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13183 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13183 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13183 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13183 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13183 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13183 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13183 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13183 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051503550228 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13183) ≤ 0.010401203841 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13183 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035141393034)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010401203841 + 2 * 0.737676 / 13183) := by gcongr
    _ ≤ (0.051503550228 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13183 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13183

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13183
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524610710 : ℝ) ≤ plow 13183 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13183) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292766741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328090890) : eMP 13183 0.011 xi bn ≤ 0.001143993554 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13183 : ℝ) * (1 - 0.011))) ≤ 0.000565696625 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001328090890 / (13183 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565696625 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565696625 : ℝ) + 3.141593 * 0.052292766741 / (13183 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143993554 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292766741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328090890) : PiBarMP 13183 12 0.011 xi bn ≤ 0.158240498331 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13183 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036442981355 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.184005009458 : ℝ) ≤ √((13183 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.817246091342 : ℝ) ≤ √(13183 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13183) ≤ 0.121344212103 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036442981355 + 0.052292766741 * 1.772454 / (2 * (114.184005009458 : ℝ))) * (1 + 0.001143993554) +
        8 / (13183 * 114.817246091342) + 0.121344212103 := by gcongr
    _ ≤ (0.158240498331 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292766741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328090890) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280179667786) :
    parallelOracle 13183 0.011 xi bn cd ≤ 0.159194821200 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13183 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13183 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524610710 : ℝ) ≤ plow 13183 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.817246091342 : ℝ) ≤ √(13183 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280179667786 : ℝ) / (2 * 0.560524610710 * 114.817246091342)) * 0.158240498331 +
        0.280179667786 ^ 2 / (2 * 0.560524610710 * 114.817246091342) := by gcongr
    _ ≤ (0.159194821200 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292766741) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001328090890)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280179667786) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13183 13183 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524610710 : ℝ) ≤ plow 13183 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.817246091342 : ℝ) ≤ √(13183 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13183 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13183 Θ 1.22 ≤ 0.011549663010 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.817246091342 := by gcongr <;> linarith
      _ ≤ (0.011549663010 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13183 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13183 13183 0.011 ≤ 0.008325290207 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13183 13183 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13183 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13183 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13183 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13183 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159194821200 + 0.011549663010 + (0.008325290207 : ℝ) *
        (1 + 2 * (0.280179667786 + 0.011549663010) / (0.560524610710 * 114.817246091342))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13183]

end BstLean.Part269.N13183

/-! The original eight local profiles supply actual 13183 moment certificates. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13183 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052292766741 ∧
    0 ≤ bN 13183 BstLean.Part154.csC (groupTheta g) ∧ bN 13183 BstLean.Part154.csC (groupTheta g) ≤ 0.001328090890 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13183 13183 0.011
      (momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13183 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13183 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13183 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228676117558 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13183 0.011
      (momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13183 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13183
/-! The actual computed-centre upper energy formula at 13183. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13183

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13183)
open BstLean.Part268 (cell13183)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084193710560
  | 2 => 0.085116501431
  | 3 => 0.086034645533
  | 4 => 0.086948904202
  | 5 => 0.087860216675
  | 6 => 0.088769728724
  | 7 => 0.089678824421
  | 8 => 0.090589161140
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13183 13183 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13183 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13183

/-! Actual upper energy certificates on all 43 source endpoints at 13183. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13183)
open BstLean.Part268 (cell13183)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13183 (gMinus 13183) (1 - (cell13183 i).lower) ≤ 1 ∧
    energyUpper 13183 (gMinus 13183) (BstLean.Part211.gPlus 13183)
      (finiteEnergy 13183 13183 0.011) (1 - (cell13183 i).lower) ≤
      (cell13183 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨10,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨11,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨12,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨13,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨14,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨15,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨16,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨17,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨18,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨19,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨20,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨21,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨22,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨23,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨24,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨25,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨26,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨27,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨28,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨29,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨30,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨31,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨32,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨33,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨34,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨35,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨36,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨37,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨38,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨39,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨40,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨41,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨42,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨43,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨44,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨45,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨46,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨47,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨48,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨49,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨50,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨51,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13183) (by norm_num)
        (q := 1 - (cell13183 ⟨52,by decide⟩).lower)
        (by norm_num [cell13183]) (by norm_num [cell13183])
      exact ⟨E.1,E.2.trans (by norm_num [cell13183])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13183

/-! Source-cell containment and simple scalar guards at 13183. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13183)
open BstLean.Part268 (cell13183)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13183 ⟨10,by decide⟩).lower ∧ (cell13183 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13183 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13183 ⟨11,by decide⟩).lower ∧ (cell13183 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13183 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13183 ⟨12,by decide⟩).lower ∧ (cell13183 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13183 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13183 ⟨13,by decide⟩).lower ∧ (cell13183 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13183 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13183 ⟨14,by decide⟩).lower ∧ (cell13183 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13183 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13183 ⟨15,by decide⟩).lower ∧ (cell13183 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13183 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13183 ⟨16,by decide⟩).lower ∧ (cell13183 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13183 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13183 ⟨17,by decide⟩).lower ∧ (cell13183 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13183 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13183 ⟨18,by decide⟩).lower ∧ (cell13183 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13183 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13183 ⟨19,by decide⟩).lower ∧ (cell13183 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13183 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13183 ⟨20,by decide⟩).lower ∧ (cell13183 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13183 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13183 ⟨21,by decide⟩).lower ∧ (cell13183 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13183 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13183 ⟨22,by decide⟩).lower ∧ (cell13183 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13183 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13183 ⟨23,by decide⟩).lower ∧ (cell13183 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13183 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13183 ⟨24,by decide⟩).lower ∧ (cell13183 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13183 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13183 ⟨25,by decide⟩).lower ∧ (cell13183 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13183 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13183 ⟨26,by decide⟩).lower ∧ (cell13183 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13183 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13183 ⟨27,by decide⟩).lower ∧ (cell13183 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13183 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13183 ⟨28,by decide⟩).lower ∧ (cell13183 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13183 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13183 ⟨29,by decide⟩).lower ∧ (cell13183 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13183 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13183 ⟨30,by decide⟩).lower ∧ (cell13183 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13183 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13183 ⟨31,by decide⟩).lower ∧ (cell13183 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13183 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13183 ⟨32,by decide⟩).lower ∧ (cell13183 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13183 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13183 ⟨33,by decide⟩).lower ∧ (cell13183 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13183 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13183 ⟨34,by decide⟩).lower ∧ (cell13183 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13183 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13183 ⟨35,by decide⟩).lower ∧ (cell13183 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13183 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13183 ⟨36,by decide⟩).lower ∧ (cell13183 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13183 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13183 ⟨37,by decide⟩).lower ∧ (cell13183 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13183 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13183 ⟨38,by decide⟩).lower ∧ (cell13183 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13183 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13183 ⟨39,by decide⟩).lower ∧ (cell13183 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13183 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13183 ⟨40,by decide⟩).lower ∧ (cell13183 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13183 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13183 ⟨41,by decide⟩).lower ∧ (cell13183 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13183 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13183 ⟨42,by decide⟩).lower ∧ (cell13183 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13183 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13183 ⟨43,by decide⟩).lower ∧ (cell13183 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13183 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13183 ⟨44,by decide⟩).lower ∧ (cell13183 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13183 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13183 ⟨45,by decide⟩).lower ∧ (cell13183 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13183 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13183 ⟨46,by decide⟩).lower ∧ (cell13183 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13183 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13183 ⟨47,by decide⟩).lower ∧ (cell13183 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13183 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13183 ⟨48,by decide⟩).lower ∧ (cell13183 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13183 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13183 ⟨49,by decide⟩).lower ∧ (cell13183 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13183 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13183 ⟨50,by decide⟩).lower ∧ (cell13183 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13183 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13183 ⟨51,by decide⟩).lower ∧ (cell13183 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13183 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13183 ⟨52,by decide⟩).lower ∧ (cell13183 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13183 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13183 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13183 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13183,cell13183,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13183 i).lower ∧
    (cell13183 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13183 i).upper ≤ (0.532 : ℝ) ∧
    (cell13183 i).centre ≤ (0.1 : ℝ) ∧ (cell13183 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13183 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13183 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13183

/-! The local source numeric instances at 13183 have no network premises. -/
namespace BstLean.Part269.N13183
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13183)
open BstLean.Part268 (cell13183)

noncomputable def sourceNumerics13183 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13183 (cell13183 i)
      scalarRow13183.M scalarRow13183.H scalarRow13183.xi := by
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
    energy_allowance := scalarRow13183.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13183]
    centre_nonneg := (scalarRow13183.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13183])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13183
/-! Actual 13184 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13184 ≤ (1.035140048773 : ℝ) := by
  have hr : (114.821600755258 : ℝ) ≤ √(13184 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.821600755258 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13184 13184 (11 / 1000) ≤
    (0.008324974464 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13184) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.821600755258 : ℝ) ≤ √(13184 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13184)
  have hdiv : K / √(13184 : ℝ) ≤ K / 114.821600755258 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.821600755258 ≤ (0.008324974464 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13184.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13184 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13184 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13184 := gPlus_lower 13184
end BstLean.Part269.N13184

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13184
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035140048772 : ℝ) ≤ wn 13184 := by
  have hn : √(13184 : ℝ) ≤ 114.821600755259 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13184 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.821600755259 ≤ 2 / √(13184 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242477278 : ℝ) ≤ rhoBar 13184 BstLean.Part154.csC ∧
    rhoBar 13184 BstLean.Part154.csC ≤ 0.000242477653 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035140048772 : ℝ) / (1.295212 * 13184) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035140048773 : ℝ) / (1.29521 * 13184) := by gcongr
      _ ≤ (0.000242477653 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13184 BstLean.Part154.csC) ≤ 0.000969969408 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13184 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) ≤ 0.000185205746 ∧
    cc1 (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) ≤ 0.000117847712 ∧
    cc2 (rhoBar 13184 BstLean.Part154.csC) ≤ 0.000068411580 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13184 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13184 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13184 BstLean.Part154.csC * nuR (rhoBar 13184 BstLean.Part154.csC)) ≤ 0.000484970005 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242477653 : ℝ) * 0.000969969408 := by gcongr
      _ ≤ (0.000484970005 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13184 BstLean.Part154.csC) * nuR (rhoBar 13184 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969969408 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13184 BstLean.Part154.csC) * rhoBar 13184 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242477653 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242477653 / 2 + 0.399 * 0.000969969408 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185205746 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484970005 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117847712 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242477653 / 1.414213562 := by gcongr
      _ ≤ (0.000068411580 : ℝ) := by norm_num

end BstLean.Part269.N13184

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13184
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) ≤ 1.48131E-7 := by
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13184 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13184 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13184 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185205746 : ℝ) ^ 2 + 0.000117847712 ^ 2 + 3 * 0.000068411580 ^ 2 +
        2 * 0.797885 * 0.000185205746 * 0.000117847712 + 2 * 0.000185205746 * 0.000068411580 +
        4 * 0.797885 * 0.000117847712 * 0.000068411580 := by gcongr
    _ ≤ (1.48131E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13184 BstLean.Part154.csC Θ ≤ 0.002529496073 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13184 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13184 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13184 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035140048773 * 1.48131E-7 / (0.000242477278 : ℝ) := by gcongr
    _ ≤ 0.002529496073 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13184 BstLean.Part154.csC Θ ≤ 0.002804789485 + 0.000639162131 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13184 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13184 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035140048773 : ℝ) * ((2 * Θ * 0.000242477653 +
        (6863 / 10000) * 0.000242477653 * 13184 * 0.000969969408) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002804789485 + 0.000639162131 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13184 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13184 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13184 0.011 Θ ∧ gammaRatio 13184 0.011 Θ ≤ 0.000083357547 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13184 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035140048773 : ℝ) * 0.525 / ((1 - 0.011) * 13184) := by gcongr
      _ ≤ (0.000083357547 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13184 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13184 0.011 Θ) :=
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
    badAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13184 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13184 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13184 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13184 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13184 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13184 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13184 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13184 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13184 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13184 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035140048773 : ℝ) * 13184 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003122265685 + 0.003168658204 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13184

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13184
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13184 BstLean.Part154.csC) (piBar (rhoBar 13184 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13184 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13184 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13184 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13184 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13184 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13184 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13184 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13184 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13184 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13184 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051501576142 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13184) ≤ 0.010400809371 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13184 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035140048773)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010400809371 + 2 * 0.737676 / 13184) := by gcongr
    _ ≤ (0.051501576142 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13184 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13184

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13184
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524652677 : ℝ) ≤ plow 13184 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13184) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292411243)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327985439) : eMP 13184 0.011 xi bn ≤ 0.001143904688 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13184 : ℝ) * (1 - 0.011))) ≤ 0.000565652713 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327985439 / (13184 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565652713 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565652713 : ℝ) + 3.141593 * 0.052292411243 / (13184 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143904688 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292411243)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327985439) : PiBarMP 13184 12 0.011 xi bn ≤ 0.158234425767 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13184 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036441534532 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.188335656493 : ℝ) ≤ √((13184 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.821600755258 : ℝ) ≤ √(13184 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13184) ≤ 0.121339610066 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036441534532 + 0.052292411243 * 1.772454 / (2 * (114.188335656493 : ℝ))) * (1 + 0.001143904688) +
        8 / (13184 * 114.821600755258) + 0.121339610066 := by gcongr
    _ ≤ (0.158234425767 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292411243)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327985439) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280176916402) :
    parallelOracle 13184 0.011 xi bn cd ≤ 0.159188683794 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13184 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13184 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524652677 : ℝ) ≤ plow 13184 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.821600755258 : ℝ) ≤ √(13184 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280176916402 : ℝ) / (2 * 0.560524652677 * 114.821600755258)) * 0.158234425767 +
        0.280176916402 ^ 2 / (2 * 0.560524652677 * 114.821600755258) := by gcongr
    _ ≤ (0.159188683794 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292411243) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327985439)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280176916402) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13184 13184 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524652677 : ℝ) ≤ plow 13184 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.821600755258 : ℝ) ≤ √(13184 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13184 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13184 Θ 1.22 ≤ 0.011549224983 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.821600755258 := by gcongr <;> linarith
      _ ≤ (0.011549224983 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13184 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13184 13184 0.011 ≤ 0.008324974464 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13184 13184 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13184 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13184 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13184 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13184 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159188683794 + 0.011549224983 + (0.008324974464 : ℝ) *
        (1 + 2 * (0.280176916402 + 0.011549224983) / (0.560524652677 * 114.821600755258))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13184]

end BstLean.Part269.N13184

/-! The original eight local profiles supply actual 13184 moment certificates. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13184 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052292411243 ∧
    0 ≤ bN 13184 BstLean.Part154.csC (groupTheta g) ∧ bN 13184 BstLean.Part154.csC (groupTheta g) ≤ 0.001327985439 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13184 13184 0.011
      (momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13184 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13184 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13184 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228675340260 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13184 0.011
      (momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13184 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13184
/-! The actual computed-centre upper energy formula at 13184. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13184

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13184)
open BstLean.Part268 (cell13184)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084191228487
  | 2 => 0.085113989460
  | 3 => 0.086032099529
  | 4 => 0.086946319037
  | 5 => 0.087857586038
  | 6 => 0.088767044911
  | 7 => 0.089676078095
  | 8 => 0.090586341061
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13184 13184 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13184 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13184

/-! Actual upper energy certificates on all 43 source endpoints at 13184. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13184)
open BstLean.Part268 (cell13184)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13184 (gMinus 13184) (1 - (cell13184 i).lower) ≤ 1 ∧
    energyUpper 13184 (gMinus 13184) (BstLean.Part211.gPlus 13184)
      (finiteEnergy 13184 13184 0.011) (1 - (cell13184 i).lower) ≤
      (cell13184 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨10,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨11,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨12,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨13,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨14,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨15,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨16,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨17,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨18,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨19,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨20,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨21,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨22,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨23,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨24,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨25,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨26,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨27,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨28,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨29,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨30,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨31,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨32,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨33,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨34,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨35,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨36,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨37,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨38,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨39,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨40,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨41,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨42,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨43,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨44,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨45,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨46,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨47,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨48,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨49,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨50,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨51,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13184) (by norm_num)
        (q := 1 - (cell13184 ⟨52,by decide⟩).lower)
        (by norm_num [cell13184]) (by norm_num [cell13184])
      exact ⟨E.1,E.2.trans (by norm_num [cell13184])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13184

/-! Source-cell containment and simple scalar guards at 13184. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13184)
open BstLean.Part268 (cell13184)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13184 ⟨10,by decide⟩).lower ∧ (cell13184 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13184 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13184 ⟨11,by decide⟩).lower ∧ (cell13184 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13184 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13184 ⟨12,by decide⟩).lower ∧ (cell13184 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13184 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13184 ⟨13,by decide⟩).lower ∧ (cell13184 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13184 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13184 ⟨14,by decide⟩).lower ∧ (cell13184 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13184 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13184 ⟨15,by decide⟩).lower ∧ (cell13184 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13184 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13184 ⟨16,by decide⟩).lower ∧ (cell13184 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13184 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13184 ⟨17,by decide⟩).lower ∧ (cell13184 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13184 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13184 ⟨18,by decide⟩).lower ∧ (cell13184 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13184 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13184 ⟨19,by decide⟩).lower ∧ (cell13184 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13184 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13184 ⟨20,by decide⟩).lower ∧ (cell13184 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13184 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13184 ⟨21,by decide⟩).lower ∧ (cell13184 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13184 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13184 ⟨22,by decide⟩).lower ∧ (cell13184 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13184 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13184 ⟨23,by decide⟩).lower ∧ (cell13184 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13184 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13184 ⟨24,by decide⟩).lower ∧ (cell13184 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13184 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13184 ⟨25,by decide⟩).lower ∧ (cell13184 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13184 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13184 ⟨26,by decide⟩).lower ∧ (cell13184 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13184 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13184 ⟨27,by decide⟩).lower ∧ (cell13184 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13184 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13184 ⟨28,by decide⟩).lower ∧ (cell13184 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13184 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13184 ⟨29,by decide⟩).lower ∧ (cell13184 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13184 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13184 ⟨30,by decide⟩).lower ∧ (cell13184 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13184 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13184 ⟨31,by decide⟩).lower ∧ (cell13184 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13184 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13184 ⟨32,by decide⟩).lower ∧ (cell13184 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13184 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13184 ⟨33,by decide⟩).lower ∧ (cell13184 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13184 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13184 ⟨34,by decide⟩).lower ∧ (cell13184 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13184 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13184 ⟨35,by decide⟩).lower ∧ (cell13184 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13184 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13184 ⟨36,by decide⟩).lower ∧ (cell13184 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13184 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13184 ⟨37,by decide⟩).lower ∧ (cell13184 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13184 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13184 ⟨38,by decide⟩).lower ∧ (cell13184 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13184 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13184 ⟨39,by decide⟩).lower ∧ (cell13184 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13184 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13184 ⟨40,by decide⟩).lower ∧ (cell13184 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13184 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13184 ⟨41,by decide⟩).lower ∧ (cell13184 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13184 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13184 ⟨42,by decide⟩).lower ∧ (cell13184 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13184 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13184 ⟨43,by decide⟩).lower ∧ (cell13184 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13184 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13184 ⟨44,by decide⟩).lower ∧ (cell13184 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13184 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13184 ⟨45,by decide⟩).lower ∧ (cell13184 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13184 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13184 ⟨46,by decide⟩).lower ∧ (cell13184 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13184 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13184 ⟨47,by decide⟩).lower ∧ (cell13184 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13184 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13184 ⟨48,by decide⟩).lower ∧ (cell13184 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13184 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13184 ⟨49,by decide⟩).lower ∧ (cell13184 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13184 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13184 ⟨50,by decide⟩).lower ∧ (cell13184 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13184 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13184 ⟨51,by decide⟩).lower ∧ (cell13184 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13184 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13184 ⟨52,by decide⟩).lower ∧ (cell13184 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13184 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13184 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13184 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13184,cell13184,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13184 i).lower ∧
    (cell13184 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13184 i).upper ≤ (0.532 : ℝ) ∧
    (cell13184 i).centre ≤ (0.1 : ℝ) ∧ (cell13184 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13184 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13184 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13184

/-! The local source numeric instances at 13184 have no network premises. -/
namespace BstLean.Part269.N13184
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13184)
open BstLean.Part268 (cell13184)

noncomputable def sourceNumerics13184 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13184 (cell13184 i)
      scalarRow13184.M scalarRow13184.H scalarRow13184.xi := by
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
    energy_allowance := scalarRow13184.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13184]
    centre_nonneg := (scalarRow13184.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13184])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13184
/-! Actual 13185 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13185 ≤ (1.035138704666 : ℝ) := by
  have hr : (114.825955254027 : ℝ) ≤ √(13185 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.825955254027 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13185 13185 (11 / 1000) ≤
    (0.008324658757 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13185) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.825955254027 : ℝ) ≤ √(13185 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13185)
  have hdiv : K / √(13185 : ℝ) ≤ K / 114.825955254027 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.825955254027 ≤ (0.008324658757 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13185.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13185 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13185 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13185 := gPlus_lower 13185
end BstLean.Part269.N13185

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13185
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035138704665 : ℝ) ≤ wn 13185 := by
  have hn : √(13185 : ℝ) ≤ 114.825955254028 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13185 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.825955254028 ≤ 2 / √(13185 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242458573 : ℝ) ≤ rhoBar 13185 BstLean.Part154.csC ∧
    rhoBar 13185 BstLean.Part154.csC ≤ 0.000242458948 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035138704665 : ℝ) / (1.295212 * 13185) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035138704666 : ℝ) / (1.29521 * 13185) := by gcongr
      _ ≤ (0.000242458948 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13185 BstLean.Part154.csC) ≤ 0.000969894579 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13185 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) ≤ 0.000185191458 ∧
    cc1 (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) ≤ 0.000117838621 ∧
    cc2 (rhoBar 13185 BstLean.Part154.csC) ≤ 0.000068406303 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13185 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13185 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13185 BstLean.Part154.csC * nuR (rhoBar 13185 BstLean.Part154.csC)) ≤ 0.000484932593 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242458948 : ℝ) * 0.000969894579 := by gcongr
      _ ≤ (0.000484932593 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13185 BstLean.Part154.csC) * nuR (rhoBar 13185 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969894579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13185 BstLean.Part154.csC) * rhoBar 13185 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242458948 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242458948 / 2 + 0.399 * 0.000969894579 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185191458 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484932593 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117838621 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242458948 / 1.414213562 := by gcongr
      _ ≤ (0.000068406303 : ℝ) := by norm_num

end BstLean.Part269.N13185

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13185
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) ≤ 1.48108E-7 := by
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13185 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13185 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13185 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185191458 : ℝ) ^ 2 + 0.000117838621 ^ 2 + 3 * 0.000068406303 ^ 2 +
        2 * 0.797885 * 0.000185191458 * 0.000117838621 + 2 * 0.000185191458 * 0.000068406303 +
        4 * 0.797885 * 0.000117838621 * 0.000068406303 := by gcongr
    _ ≤ (1.48108E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13185 BstLean.Part154.csC Θ ≤ 0.002529295152 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13185 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13185 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13185 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035138704666 * 1.48108E-7 / (0.000242458573 : ℝ) := by gcongr
    _ ≤ 0.002529295152 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13185 BstLean.Part154.csC Θ ≤ 0.002804565827 + 0.000639111996 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13185 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13185 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035138704666 : ℝ) * ((2 * Θ * 0.000242458948 +
        (6863 / 10000) * 0.000242458948 * 13185 * 0.000969894579) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002804565827 + 0.000639111996 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13185 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13185 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13185 0.011 Θ ∧ gammaRatio 13185 0.011 Θ ≤ 0.000083351117 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13185 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035138704666 : ℝ) * 0.525 / ((1 - 0.011) * 13185) := by gcongr
      _ ≤ (0.000083351117 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13185 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13185 0.011 Θ) :=
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
    badAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13185 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13185 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13185 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13185 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13185 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13185 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13185 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13185 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13185 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13185 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035138704666 : ℝ) * 13185 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003122042027 + 0.003168407148 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13185

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13185
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13185 BstLean.Part154.csC) (piBar (rhoBar 13185 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13185 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13185 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13185 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13185 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13185 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13185 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13185 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13185 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13185 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13185 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051499602278 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13185) ≤ 0.010400414945 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13185 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035138704666)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010400414945 + 2 * 0.737676 / 13185) := by gcongr
    _ ≤ (0.051499602278 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13185 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13185

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13185
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524694637 : ℝ) ≤ plow 13185 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13185) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292055780)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327879955) : eMP 13185 0.011 xi bn ≤ 0.001143815815 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13185 : ℝ) * (1 - 0.011))) ≤ 0.000565608797 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327879955 / (13185 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565608797 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565608797 : ℝ) + 3.141593 * 0.052292055780 / (13185 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143815815 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292055780)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327879955) : PiBarMP 13185 12 0.011 xi bn ≤ 0.158228353220 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13185 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036440087199 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.192666139292 : ℝ) ≤ √((13185 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.825955254027 : ℝ) ≤ √(13185 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13185) ≤ 0.121335008553 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036440087199 + 0.052292055780 * 1.772454 / (2 * (114.192666139292 : ℝ))) * (1 + 0.001143815815) +
        8 / (13185 * 114.825955254027) + 0.121335008553 := by gcongr
    _ ≤ (0.158228353220 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292055780)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327879955) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280174165315) :
    parallelOracle 13185 0.011 xi bn cd ≤ 0.159182546413 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13185 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13185 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524694637 : ℝ) ≤ plow 13185 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.825955254027 : ℝ) ≤ √(13185 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280174165315 : ℝ) / (2 * 0.560524694637 * 114.825955254027)) * 0.158228353220 +
        0.280174165315 ^ 2 / (2 * 0.560524694637 * 114.825955254027) := by gcongr
    _ ≤ (0.159182546413 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052292055780) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327879955)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280174165315) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13185 13185 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524694637 : ℝ) ≤ plow 13185 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.825955254027 : ℝ) ≤ √(13185 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13185 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13185 Θ 1.22 ≤ 0.011548787007 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.825955254027 := by gcongr <;> linarith
      _ ≤ (0.011548787007 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13185 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13185 13185 0.011 ≤ 0.008324658757 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13185 13185 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13185 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13185 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13185 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13185 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159182546413 + 0.011548787007 + (0.008324658757 : ℝ) *
        (1 + 2 * (0.280174165315 + 0.011548787007) / (0.560524694637 * 114.825955254027))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13185]

end BstLean.Part269.N13185

/-! The original eight local profiles supply actual 13185 moment certificates. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13185 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052292055780 ∧
    0 ≤ bN 13185 BstLean.Part154.csC (groupTheta g) ∧ bN 13185 BstLean.Part154.csC (groupTheta g) ≤ 0.001327879955 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13185 13185 0.011
      (momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13185 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13185 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13185 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228674563037 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13185 0.011
      (momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13185 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13185
/-! The actual computed-centre upper energy formula at 13185. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13185

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13185)
open BstLean.Part268 (cell13185)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084188747100
  | 2 => 0.085111478196
  | 3 => 0.086029554262
  | 4 => 0.086943734643
  | 5 => 0.087854956214
  | 6 => 0.088764361963
  | 7 => 0.089673332697
  | 8 => 0.090583521986
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13185 13185 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13185 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13185

/-! Actual upper energy certificates on all 43 source endpoints at 13185. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13185)
open BstLean.Part268 (cell13185)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13185 (gMinus 13185) (1 - (cell13185 i).lower) ≤ 1 ∧
    energyUpper 13185 (gMinus 13185) (BstLean.Part211.gPlus 13185)
      (finiteEnergy 13185 13185 0.011) (1 - (cell13185 i).lower) ≤
      (cell13185 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨10,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨11,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨12,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨13,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨14,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨15,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨16,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨17,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨18,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨19,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨20,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨21,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨22,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨23,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨24,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨25,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨26,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨27,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨28,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨29,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨30,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨31,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨32,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨33,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨34,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨35,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨36,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨37,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨38,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨39,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨40,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨41,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨42,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨43,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨44,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨45,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨46,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨47,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨48,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨49,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨50,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨51,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13185) (by norm_num)
        (q := 1 - (cell13185 ⟨52,by decide⟩).lower)
        (by norm_num [cell13185]) (by norm_num [cell13185])
      exact ⟨E.1,E.2.trans (by norm_num [cell13185])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13185

/-! Source-cell containment and simple scalar guards at 13185. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13185)
open BstLean.Part268 (cell13185)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13185 ⟨10,by decide⟩).lower ∧ (cell13185 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13185 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13185 ⟨11,by decide⟩).lower ∧ (cell13185 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13185 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13185 ⟨12,by decide⟩).lower ∧ (cell13185 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13185 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13185 ⟨13,by decide⟩).lower ∧ (cell13185 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13185 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13185 ⟨14,by decide⟩).lower ∧ (cell13185 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13185 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13185 ⟨15,by decide⟩).lower ∧ (cell13185 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13185 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13185 ⟨16,by decide⟩).lower ∧ (cell13185 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13185 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13185 ⟨17,by decide⟩).lower ∧ (cell13185 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13185 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13185 ⟨18,by decide⟩).lower ∧ (cell13185 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13185 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13185 ⟨19,by decide⟩).lower ∧ (cell13185 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13185 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13185 ⟨20,by decide⟩).lower ∧ (cell13185 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13185 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13185 ⟨21,by decide⟩).lower ∧ (cell13185 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13185 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13185 ⟨22,by decide⟩).lower ∧ (cell13185 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13185 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13185 ⟨23,by decide⟩).lower ∧ (cell13185 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13185 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13185 ⟨24,by decide⟩).lower ∧ (cell13185 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13185 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13185 ⟨25,by decide⟩).lower ∧ (cell13185 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13185 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13185 ⟨26,by decide⟩).lower ∧ (cell13185 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13185 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13185 ⟨27,by decide⟩).lower ∧ (cell13185 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13185 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13185 ⟨28,by decide⟩).lower ∧ (cell13185 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13185 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13185 ⟨29,by decide⟩).lower ∧ (cell13185 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13185 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13185 ⟨30,by decide⟩).lower ∧ (cell13185 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13185 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13185 ⟨31,by decide⟩).lower ∧ (cell13185 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13185 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13185 ⟨32,by decide⟩).lower ∧ (cell13185 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13185 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13185 ⟨33,by decide⟩).lower ∧ (cell13185 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13185 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13185 ⟨34,by decide⟩).lower ∧ (cell13185 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13185 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13185 ⟨35,by decide⟩).lower ∧ (cell13185 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13185 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13185 ⟨36,by decide⟩).lower ∧ (cell13185 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13185 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13185 ⟨37,by decide⟩).lower ∧ (cell13185 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13185 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13185 ⟨38,by decide⟩).lower ∧ (cell13185 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13185 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13185 ⟨39,by decide⟩).lower ∧ (cell13185 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13185 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13185 ⟨40,by decide⟩).lower ∧ (cell13185 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13185 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13185 ⟨41,by decide⟩).lower ∧ (cell13185 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13185 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13185 ⟨42,by decide⟩).lower ∧ (cell13185 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13185 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13185 ⟨43,by decide⟩).lower ∧ (cell13185 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13185 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13185 ⟨44,by decide⟩).lower ∧ (cell13185 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13185 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13185 ⟨45,by decide⟩).lower ∧ (cell13185 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13185 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13185 ⟨46,by decide⟩).lower ∧ (cell13185 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13185 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13185 ⟨47,by decide⟩).lower ∧ (cell13185 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13185 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13185 ⟨48,by decide⟩).lower ∧ (cell13185 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13185 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13185 ⟨49,by decide⟩).lower ∧ (cell13185 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13185 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13185 ⟨50,by decide⟩).lower ∧ (cell13185 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13185 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13185 ⟨51,by decide⟩).lower ∧ (cell13185 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13185 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13185 ⟨52,by decide⟩).lower ∧ (cell13185 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13185 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13185 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13185 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13185,cell13185,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13185 i).lower ∧
    (cell13185 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13185 i).upper ≤ (0.532 : ℝ) ∧
    (cell13185 i).centre ≤ (0.1 : ℝ) ∧ (cell13185 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13185 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13185 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13185

/-! The local source numeric instances at 13185 have no network premises. -/
namespace BstLean.Part269.N13185
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13185)
open BstLean.Part268 (cell13185)

noncomputable def sourceNumerics13185 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13185 (cell13185 i)
      scalarRow13185.M scalarRow13185.H scalarRow13185.xi := by
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
    energy_allowance := scalarRow13185.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13185]
    centre_nonneg := (scalarRow13185.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13185])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13185
/-! Actual 13186 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13186 ≤ (1.035137360713 : ℝ) := by
  have hr : (114.830309587669 : ℝ) ≤ √(13186 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.830309587669 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13186 13186 (11 / 1000) ≤
    (0.008324343086 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13186) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.830309587669 : ℝ) ≤ √(13186 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13186)
  have hdiv : K / √(13186 : ℝ) ≤ K / 114.830309587669 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.830309587669 ≤ (0.008324343086 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13186.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13186 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13186 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13186 := gPlus_lower 13186
end BstLean.Part269.N13186

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13186
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035137360712 : ℝ) ≤ wn 13186 := by
  have hn : √(13186 : ℝ) ≤ 114.830309587670 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13186 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.830309587670 ≤ 2 / √(13186 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242439870 : ℝ) ≤ rhoBar 13186 BstLean.Part154.csC ∧
    rhoBar 13186 BstLean.Part154.csC ≤ 0.000242440246 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035137360712 : ℝ) / (1.295212 * 13186) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035137360713 : ℝ) / (1.29521 * 13186) := by gcongr
      _ ≤ (0.000242440246 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13186 BstLean.Part154.csC) ≤ 0.000969819762 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13186 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) ≤ 0.000185177173 ∧
    cc1 (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) ≤ 0.000117829531 ∧
    cc2 (rhoBar 13186 BstLean.Part154.csC) ≤ 0.000068401026 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13186 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13186 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13186 BstLean.Part154.csC * nuR (rhoBar 13186 BstLean.Part154.csC)) ≤ 0.000484895187 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242440246 : ℝ) * 0.000969819762 := by gcongr
      _ ≤ (0.000484895187 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13186 BstLean.Part154.csC) * nuR (rhoBar 13186 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969819762 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13186 BstLean.Part154.csC) * rhoBar 13186 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242440246 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242440246 / 2 + 0.399 * 0.000969819762 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185177173 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484895187 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117829531 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242440246 / 1.414213562 := by gcongr
      _ ≤ (0.000068401026 : ℝ) := by norm_num

end BstLean.Part269.N13186

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13186
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) ≤ 1.48085E-7 := by
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13186 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13186 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13186 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185177173 : ℝ) ^ 2 + 0.000117829531 ^ 2 + 3 * 0.000068401026 ^ 2 +
        2 * 0.797885 * 0.000185177173 * 0.000117829531 + 2 * 0.000185177173 * 0.000068401026 +
        4 * 0.797885 * 0.000117829531 * 0.000068401026 := by gcongr
    _ ≤ (1.48085E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13186 BstLean.Part154.csC Θ ≤ 0.002529094181 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13186 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13186 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13186 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035137360713 * 1.48085E-7 / (0.000242439870 : ℝ) := by gcongr
    _ ≤ 0.002529094181 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13186 BstLean.Part154.csC Θ ≤ 0.002804342208 + 0.000639061868 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13186 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13186 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035137360713 : ℝ) * ((2 * Θ * 0.000242440246 +
        (6863 / 10000) * 0.000242440246 * 13186 * 0.000969819762) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002804342208 + 0.000639061868 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13186 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13186 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13186 0.011 Θ ∧ gammaRatio 13186 0.011 Θ ≤ 0.000083344687 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13186 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035137360713 : ℝ) * 0.525 / ((1 - 0.011) * 13186) := by gcongr
      _ ≤ (0.000083344687 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13186 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13186 0.011 Θ) :=
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
    badAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13186 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13186 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13186 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13186 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13186 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13186 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13186 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13186 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13186 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13186 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035137360713 : ℝ) * 13186 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003121818408 + 0.003168156049 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13186

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13186
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13186 BstLean.Part154.csC) (piBar (rhoBar 13186 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13186 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13186 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13186 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13186 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13186 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13186 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13186 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13186 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13186 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13186 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051497628640 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13186) ≤ 0.010400020564 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13186 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035137360713)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010400020564 + 2 * 0.737676 / 13186) := by gcongr
    _ ≤ (0.051497628640 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13186 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13186

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13186
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524736591 : ℝ) ≤ plow 13186 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13186) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291700334)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327774446) : eMP 13186 0.011 xi bn ≤ 0.001143726938 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13186 : ℝ) * (1 - 0.011))) ≤ 0.000565564879 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327774446 / (13186 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565564879 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565564879 : ℝ) + 3.141593 * 0.052291700334 / (13186 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143726938 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291700334)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327774446) : PiBarMP 13186 12 0.011 xi bn ≤ 0.158222280796 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13186 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036438639465 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.196996457875 : ℝ) ≤ √((13186 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.830309587669 : ℝ) ≤ √(13186 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13186) ≤ 0.121330407563 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036438639465 + 0.052291700334 * 1.772454 / (2 * (114.196996457875 : ℝ))) * (1 + 0.001143726938) +
        8 / (13186 * 114.830309587669) + 0.121330407563 := by gcongr
    _ ≤ (0.158222280796 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291700334)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327774446) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280171414488) :
    parallelOracle 13186 0.011 xi bn cd ≤ 0.159176409163 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13186 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13186 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524736591 : ℝ) ≤ plow 13186 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.830309587669 : ℝ) ≤ √(13186 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280171414488 : ℝ) / (2 * 0.560524736591 * 114.830309587669)) * 0.158222280796 +
        0.280171414488 ^ 2 / (2 * 0.560524736591 * 114.830309587669) := by gcongr
    _ ≤ (0.159176409163 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291700334) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327774446)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280171414488) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13186 13186 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524736591 : ℝ) ≤ plow 13186 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.830309587669 : ℝ) ≤ √(13186 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13186 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13186 Θ 1.22 ≤ 0.011548349080 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.830309587669 := by gcongr <;> linarith
      _ ≤ (0.011548349080 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13186 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13186 13186 0.011 ≤ 0.008324343086 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13186 13186 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13186 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13186 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13186 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13186 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159176409163 + 0.011548349080 + (0.008324343086 : ℝ) *
        (1 + 2 * (0.280171414488 + 0.011548349080) / (0.560524736591 * 114.830309587669))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13186]

end BstLean.Part269.N13186

/-! The original eight local profiles supply actual 13186 moment certificates. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13186 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052291700334 ∧
    0 ≤ bN 13186 BstLean.Part154.csC (groupTheta g) ∧ bN 13186 BstLean.Part154.csC (groupTheta g) ≤ 0.001327774446 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13186 13186 0.011
      (momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13186 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13186 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13186 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228673785848 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13186 0.011
      (momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13186 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13186
/-! The actual computed-centre upper energy formula at 13186. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13186

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13186)
open BstLean.Part268 (cell13186)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084186266397
  | 2 => 0.085108967640
  | 3 => 0.086027009729
  | 4 => 0.086941151018
  | 5 => 0.087852327202
  | 6 => 0.088761679879
  | 7 => 0.089670588225
  | 8 => 0.090580703916
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13186 13186 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13186 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13186

/-! Actual upper energy certificates on all 43 source endpoints at 13186. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13186)
open BstLean.Part268 (cell13186)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13186 (gMinus 13186) (1 - (cell13186 i).lower) ≤ 1 ∧
    energyUpper 13186 (gMinus 13186) (BstLean.Part211.gPlus 13186)
      (finiteEnergy 13186 13186 0.011) (1 - (cell13186 i).lower) ≤
      (cell13186 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨10,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨11,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨12,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨13,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨14,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨15,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨16,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨17,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨18,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨19,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨20,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨21,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨22,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨23,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨24,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨25,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨26,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨27,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨28,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨29,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨30,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨31,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨32,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨33,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨34,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨35,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨36,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨37,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨38,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨39,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨40,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨41,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨42,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨43,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨44,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨45,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨46,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨47,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨48,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨49,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨50,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨51,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13186) (by norm_num)
        (q := 1 - (cell13186 ⟨52,by decide⟩).lower)
        (by norm_num [cell13186]) (by norm_num [cell13186])
      exact ⟨E.1,E.2.trans (by norm_num [cell13186])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13186

/-! Source-cell containment and simple scalar guards at 13186. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13186)
open BstLean.Part268 (cell13186)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13186 ⟨10,by decide⟩).lower ∧ (cell13186 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13186 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13186 ⟨11,by decide⟩).lower ∧ (cell13186 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13186 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13186 ⟨12,by decide⟩).lower ∧ (cell13186 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13186 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13186 ⟨13,by decide⟩).lower ∧ (cell13186 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13186 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13186 ⟨14,by decide⟩).lower ∧ (cell13186 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13186 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13186 ⟨15,by decide⟩).lower ∧ (cell13186 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13186 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13186 ⟨16,by decide⟩).lower ∧ (cell13186 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13186 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13186 ⟨17,by decide⟩).lower ∧ (cell13186 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13186 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13186 ⟨18,by decide⟩).lower ∧ (cell13186 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13186 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13186 ⟨19,by decide⟩).lower ∧ (cell13186 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13186 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13186 ⟨20,by decide⟩).lower ∧ (cell13186 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13186 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13186 ⟨21,by decide⟩).lower ∧ (cell13186 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13186 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13186 ⟨22,by decide⟩).lower ∧ (cell13186 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13186 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13186 ⟨23,by decide⟩).lower ∧ (cell13186 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13186 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13186 ⟨24,by decide⟩).lower ∧ (cell13186 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13186 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13186 ⟨25,by decide⟩).lower ∧ (cell13186 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13186 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13186 ⟨26,by decide⟩).lower ∧ (cell13186 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13186 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13186 ⟨27,by decide⟩).lower ∧ (cell13186 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13186 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13186 ⟨28,by decide⟩).lower ∧ (cell13186 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13186 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13186 ⟨29,by decide⟩).lower ∧ (cell13186 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13186 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13186 ⟨30,by decide⟩).lower ∧ (cell13186 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13186 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13186 ⟨31,by decide⟩).lower ∧ (cell13186 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13186 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13186 ⟨32,by decide⟩).lower ∧ (cell13186 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13186 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13186 ⟨33,by decide⟩).lower ∧ (cell13186 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13186 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13186 ⟨34,by decide⟩).lower ∧ (cell13186 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13186 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13186 ⟨35,by decide⟩).lower ∧ (cell13186 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13186 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13186 ⟨36,by decide⟩).lower ∧ (cell13186 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13186 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13186 ⟨37,by decide⟩).lower ∧ (cell13186 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13186 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13186 ⟨38,by decide⟩).lower ∧ (cell13186 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13186 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13186 ⟨39,by decide⟩).lower ∧ (cell13186 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13186 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13186 ⟨40,by decide⟩).lower ∧ (cell13186 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13186 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13186 ⟨41,by decide⟩).lower ∧ (cell13186 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13186 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13186 ⟨42,by decide⟩).lower ∧ (cell13186 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13186 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13186 ⟨43,by decide⟩).lower ∧ (cell13186 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13186 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13186 ⟨44,by decide⟩).lower ∧ (cell13186 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13186 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13186 ⟨45,by decide⟩).lower ∧ (cell13186 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13186 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13186 ⟨46,by decide⟩).lower ∧ (cell13186 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13186 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13186 ⟨47,by decide⟩).lower ∧ (cell13186 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13186 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13186 ⟨48,by decide⟩).lower ∧ (cell13186 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13186 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13186 ⟨49,by decide⟩).lower ∧ (cell13186 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13186 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13186 ⟨50,by decide⟩).lower ∧ (cell13186 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13186 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13186 ⟨51,by decide⟩).lower ∧ (cell13186 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13186 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13186 ⟨52,by decide⟩).lower ∧ (cell13186 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13186 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13186 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13186 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13186,cell13186,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13186 i).lower ∧
    (cell13186 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13186 i).upper ≤ (0.532 : ℝ) ∧
    (cell13186 i).centre ≤ (0.1 : ℝ) ∧ (cell13186 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13186 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13186 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13186

/-! The local source numeric instances at 13186 have no network premises. -/
namespace BstLean.Part269.N13186
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13186)
open BstLean.Part268 (cell13186)

noncomputable def sourceNumerics13186 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13186 (cell13186 i)
      scalarRow13186.M scalarRow13186.H scalarRow13186.xi := by
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
    energy_allowance := scalarRow13186.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13186]
    centre_nonneg := (scalarRow13186.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13186])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13186
/-! Actual 13187 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13187 ≤ (1.035136016913 : ℝ) := by
  have hr : (114.834663756202 : ℝ) ≤ √(13187 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.834663756202 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13187 13187 (11 / 1000) ≤
    (0.008324027451 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13187) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.834663756202 : ℝ) ≤ √(13187 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13187)
  have hdiv : K / √(13187 : ℝ) ≤ K / 114.834663756202 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.834663756202 ≤ (0.008324027451 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13187.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13187 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13187 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13187 := gPlus_lower 13187
end BstLean.Part269.N13187

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13187
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035136016912 : ℝ) ≤ wn 13187 := by
  have hn : √(13187 : ℝ) ≤ 114.834663756203 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13187 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.834663756203 ≤ 2 / √(13187 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242421171 : ℝ) ≤ rhoBar 13187 BstLean.Part154.csC ∧
    rhoBar 13187 BstLean.Part154.csC ≤ 0.000242421546 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035136016912 : ℝ) / (1.295212 * 13187) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035136016913 : ℝ) / (1.29521 * 13187) := by gcongr
      _ ≤ (0.000242421546 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13187 BstLean.Part154.csC) ≤ 0.000969744953 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13187 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) ≤ 0.000185162889 ∧
    cc1 (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) ≤ 0.000117820442 ∧
    cc2 (rhoBar 13187 BstLean.Part154.csC) ≤ 0.000068395750 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13187 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13187 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13187 BstLean.Part154.csC * nuR (rhoBar 13187 BstLean.Part154.csC)) ≤ 0.000484857785 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242421546 : ℝ) * 0.000969744953 := by gcongr
      _ ≤ (0.000484857785 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13187 BstLean.Part154.csC) * nuR (rhoBar 13187 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969744953 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13187 BstLean.Part154.csC) * rhoBar 13187 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242421546 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242421546 / 2 + 0.399 * 0.000969744953 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185162889 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484857785 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117820442 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242421546 / 1.414213562 := by gcongr
      _ ≤ (0.000068395750 : ℝ) := by norm_num

end BstLean.Part269.N13187

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13187
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) ≤ 1.48062E-7 := by
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13187 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13187 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13187 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185162889 : ℝ) ^ 2 + 0.000117820442 ^ 2 + 3 * 0.000068395750 ^ 2 +
        2 * 0.797885 * 0.000185162889 * 0.000117820442 + 2 * 0.000185162889 * 0.000068395750 +
        4 * 0.797885 * 0.000117820442 * 0.000068395750 := by gcongr
    _ ≤ (1.48062E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13187 BstLean.Part154.csC Θ ≤ 0.002528893138 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13187 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13187 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13187 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035136016913 * 1.48062E-7 / (0.000242421171 : ℝ) := by gcongr
    _ ≤ 0.002528893138 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13187 BstLean.Part154.csC Θ ≤ 0.002804118603 + 0.000639011746 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13187 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13187 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035136016913 : ℝ) * ((2 * Θ * 0.000242421546 +
        (6863 / 10000) * 0.000242421546 * 13187 * 0.000969744953) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002804118603 + 0.000639011746 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13187 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13187 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13187 0.011 Θ ∧ gammaRatio 13187 0.011 Θ ≤ 0.000083338259 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13187 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035136016913 : ℝ) * 0.525 / ((1 - 0.011) * 13187) := by gcongr
      _ ≤ (0.000083338259 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13187 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13187 0.011 Θ) :=
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
    badAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13187 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13187 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13187 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13187 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13187 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13187 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13187 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13187 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13187 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13187 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035136016913 : ℝ) * 13187 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003121594803 + 0.003167904884 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13187

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13187
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13187 BstLean.Part154.csC) (piBar (rhoBar 13187 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13187 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13187 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13187 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13187 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13187 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13187 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13187 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13187 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13187 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13187 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051495655230 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13187) ≤ 0.010399626228 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13187 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035136016913)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010399626228 + 2 * 0.737676 / 13187) := by gcongr
    _ ≤ (0.051495655230 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13187 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13187

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13187
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524778539 : ℝ) ≤ plow 13187 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13187) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291344868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327668898) : eMP 13187 0.011 xi bn ≤ 0.001143638051 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13187 : ℝ) * (1 - 0.011))) ≤ 0.000565520956 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327668898 / (13187 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565520956 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565520956 : ℝ) + 3.141593 * 0.052291344868 / (13187 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143638051 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291344868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327668898) : PiBarMP 13187 12 0.011 xi bn ≤ 0.158216208303 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13187 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036437191138 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.201326612259 : ℝ) ≤ √((13187 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.834663756202 : ℝ) ≤ √(13187 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13187) ≤ 0.121325807096 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036437191138 + 0.052291344868 * 1.772454 / (2 * (114.201326612259 : ℝ))) * (1 + 0.001143638051) +
        8 / (13187 * 114.834663756202) + 0.121325807096 := by gcongr
    _ ≤ (0.158216208303 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291344868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327668898) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280168663843) :
    parallelOracle 13187 0.011 xi bn cd ≤ 0.159170271852 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13187 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13187 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524778539 : ℝ) ≤ plow 13187 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.834663756202 : ℝ) ≤ √(13187 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280168663843 : ℝ) / (2 * 0.560524778539 * 114.834663756202)) * 0.158216208303 +
        0.280168663843 ^ 2 / (2 * 0.560524778539 * 114.834663756202) := by gcongr
    _ ≤ (0.159170271852 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052291344868) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327668898)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280168663843) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13187 13187 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524778539 : ℝ) ≤ plow 13187 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.834663756202 : ℝ) ≤ √(13187 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13187 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13187 Θ 1.22 ≤ 0.011547911203 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.834663756202 := by gcongr <;> linarith
      _ ≤ (0.011547911203 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13187 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13187 13187 0.011 ≤ 0.008324027451 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13187 13187 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13187 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13187 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13187 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13187 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159170271852 + 0.011547911203 + (0.008324027451 : ℝ) *
        (1 + 2 * (0.280168663843 + 0.011547911203) / (0.560524778539 * 114.834663756202))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13187]

end BstLean.Part269.N13187

/-! The original eight local profiles supply actual 13187 moment certificates. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13187 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052291344868 ∧
    0 ≤ bN 13187 BstLean.Part154.csC (groupTheta g) ∧ bN 13187 BstLean.Part154.csC (groupTheta g) ≤ 0.001327668898 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13187 13187 0.011
      (momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13187 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13187 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13187 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228673008613 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13187 0.011
      (momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13187 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13187
/-! The actual computed-centre upper energy formula at 13187. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13187

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13187)
open BstLean.Part268 (cell13187)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084183786378
  | 2 => 0.085106457790
  | 3 => 0.086024465930
  | 4 => 0.086938568161
  | 5 => 0.087849699001
  | 6 => 0.088758998657
  | 7 => 0.089667844680
  | 8 => 0.090577886847
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13187 13187 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13187 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13187

/-! Actual upper energy certificates on all 43 source endpoints at 13187. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13187)
open BstLean.Part268 (cell13187)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13187 (gMinus 13187) (1 - (cell13187 i).lower) ≤ 1 ∧
    energyUpper 13187 (gMinus 13187) (BstLean.Part211.gPlus 13187)
      (finiteEnergy 13187 13187 0.011) (1 - (cell13187 i).lower) ≤
      (cell13187 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨10,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨11,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨12,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨13,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨14,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨15,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨16,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨17,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨18,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨19,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨20,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨21,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨22,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨23,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨24,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨25,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨26,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨27,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨28,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨29,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨30,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨31,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨32,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨33,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨34,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨35,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨36,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨37,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨38,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨39,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨40,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨41,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨42,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨43,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨44,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨45,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨46,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨47,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨48,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨49,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨50,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨51,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13187) (by norm_num)
        (q := 1 - (cell13187 ⟨52,by decide⟩).lower)
        (by norm_num [cell13187]) (by norm_num [cell13187])
      exact ⟨E.1,E.2.trans (by norm_num [cell13187])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13187

/-! Source-cell containment and simple scalar guards at 13187. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13187)
open BstLean.Part268 (cell13187)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13187 ⟨10,by decide⟩).lower ∧ (cell13187 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13187 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13187 ⟨11,by decide⟩).lower ∧ (cell13187 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13187 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13187 ⟨12,by decide⟩).lower ∧ (cell13187 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13187 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13187 ⟨13,by decide⟩).lower ∧ (cell13187 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13187 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13187 ⟨14,by decide⟩).lower ∧ (cell13187 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13187 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13187 ⟨15,by decide⟩).lower ∧ (cell13187 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13187 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13187 ⟨16,by decide⟩).lower ∧ (cell13187 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13187 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13187 ⟨17,by decide⟩).lower ∧ (cell13187 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13187 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13187 ⟨18,by decide⟩).lower ∧ (cell13187 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13187 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13187 ⟨19,by decide⟩).lower ∧ (cell13187 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13187 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13187 ⟨20,by decide⟩).lower ∧ (cell13187 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13187 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13187 ⟨21,by decide⟩).lower ∧ (cell13187 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13187 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13187 ⟨22,by decide⟩).lower ∧ (cell13187 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13187 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13187 ⟨23,by decide⟩).lower ∧ (cell13187 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13187 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13187 ⟨24,by decide⟩).lower ∧ (cell13187 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13187 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13187 ⟨25,by decide⟩).lower ∧ (cell13187 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13187 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13187 ⟨26,by decide⟩).lower ∧ (cell13187 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13187 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13187 ⟨27,by decide⟩).lower ∧ (cell13187 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13187 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13187 ⟨28,by decide⟩).lower ∧ (cell13187 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13187 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13187 ⟨29,by decide⟩).lower ∧ (cell13187 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13187 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13187 ⟨30,by decide⟩).lower ∧ (cell13187 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13187 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13187 ⟨31,by decide⟩).lower ∧ (cell13187 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13187 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13187 ⟨32,by decide⟩).lower ∧ (cell13187 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13187 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13187 ⟨33,by decide⟩).lower ∧ (cell13187 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13187 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13187 ⟨34,by decide⟩).lower ∧ (cell13187 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13187 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13187 ⟨35,by decide⟩).lower ∧ (cell13187 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13187 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13187 ⟨36,by decide⟩).lower ∧ (cell13187 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13187 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13187 ⟨37,by decide⟩).lower ∧ (cell13187 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13187 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13187 ⟨38,by decide⟩).lower ∧ (cell13187 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13187 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13187 ⟨39,by decide⟩).lower ∧ (cell13187 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13187 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13187 ⟨40,by decide⟩).lower ∧ (cell13187 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13187 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13187 ⟨41,by decide⟩).lower ∧ (cell13187 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13187 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13187 ⟨42,by decide⟩).lower ∧ (cell13187 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13187 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13187 ⟨43,by decide⟩).lower ∧ (cell13187 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13187 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13187 ⟨44,by decide⟩).lower ∧ (cell13187 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13187 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13187 ⟨45,by decide⟩).lower ∧ (cell13187 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13187 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13187 ⟨46,by decide⟩).lower ∧ (cell13187 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13187 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13187 ⟨47,by decide⟩).lower ∧ (cell13187 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13187 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13187 ⟨48,by decide⟩).lower ∧ (cell13187 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13187 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13187 ⟨49,by decide⟩).lower ∧ (cell13187 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13187 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13187 ⟨50,by decide⟩).lower ∧ (cell13187 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13187 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13187 ⟨51,by decide⟩).lower ∧ (cell13187 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13187 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13187 ⟨52,by decide⟩).lower ∧ (cell13187 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13187 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13187 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13187 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13187,cell13187,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13187 i).lower ∧
    (cell13187 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13187 i).upper ≤ (0.532 : ℝ) ∧
    (cell13187 i).centre ≤ (0.1 : ℝ) ∧ (cell13187 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13187 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13187 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13187

/-! The local source numeric instances at 13187 have no network premises. -/
namespace BstLean.Part269.N13187
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13187)
open BstLean.Part268 (cell13187)

noncomputable def sourceNumerics13187 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13187 (cell13187 i)
      scalarRow13187.M scalarRow13187.H scalarRow13187.xi := by
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
    energy_allowance := scalarRow13187.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13187]
    centre_nonneg := (scalarRow13187.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13187])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13187