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
/-! Actual 12838 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12838 ≤ (1.035614550053 : ℝ) := by
  have hr : (113.304898393670 : ℝ) ≤ √(12838 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.304898393670 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12838 12838 (11 / 1000) ≤
    (0.008436413634 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12838) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.304898393670 : ℝ) ≤ √(12838 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12838)
  have hdiv : K / √(12838 : ℝ) ≤ K / 113.304898393670 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.304898393670 ≤ (0.008436413634 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12838.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12838 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12838 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12838 := gPlus_lower 12838
end BstLean.Part269.N12838

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12838
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035614550052 : ℝ) ≤ wn 12838 := by
  have hn : √(12838 : ℝ) ≤ 113.304898393671 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12838 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.304898393671 ≤ 2 / √(12838 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249126487 : ℝ) ≤ rhoBar 12838 BstLean.Part154.csC ∧
    rhoBar 12838 BstLean.Part154.csC ≤ 0.000249126872 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035614550052 : ℝ) / (1.295212 * 12838) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035614550053 : ℝ) / (1.29521 * 12838) := by gcongr
      _ ≤ (0.000249126872 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12838 BstLean.Part154.csC) ≤ 0.000996569553 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12838 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) ≤ 0.000190284689 ∧
    cc1 (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) ≤ 0.000121079431 ∧
    cc2 (rhoBar 12838 BstLean.Part154.csC) ≤ 0.000070287561 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12838 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12838 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12838 BstLean.Part154.csC * nuR (rhoBar 12838 BstLean.Part154.csC)) ≤ 0.000498269261 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249126872 : ℝ) * 0.000996569553 := by gcongr
      _ ≤ (0.000498269261 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12838 BstLean.Part154.csC) * nuR (rhoBar 12838 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996569553 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12838 BstLean.Part154.csC) * rhoBar 12838 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249126872 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249126872 / 2 + 0.399 * 0.000996569553 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190284689 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498269261 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121079431 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249126872 / 1.414213562 := by gcongr
      _ ≤ (0.000070287561 : ℝ) := by norm_num

end BstLean.Part269.N12838

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12838
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) ≤ 1.56366E-7 := by
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12838 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12838 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12838 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190284689 : ℝ) ^ 2 + 0.000121079431 ^ 2 + 3 * 0.000070287561 ^ 2 +
        2 * 0.797885 * 0.000190284689 * 0.000121079431 + 2 * 0.000190284689 * 0.000070287561 +
        4 * 0.797885 * 0.000121079431 * 0.000070287561 := by gcongr
    _ ≤ (1.56366E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12838 BstLean.Part154.csC Θ ≤ 0.002600043162 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12838 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12838 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12838 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035614550053 * 1.56366E-7 / (0.000249126487 : ℝ) := by gcongr
    _ ≤ 0.002600043162 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12838 BstLean.Part154.csC Θ ≤ 0.002884349694 + 0.000656990249 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12838 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12838 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035614550053 : ℝ) * ((2 * Θ * 0.000249126872 +
        (6863 / 10000) * 0.000249126872 * 12838 * 0.000996569553) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002884349694 + 0.000656990249 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12838 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12838 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12838 0.011 Θ ∧ gammaRatio 12838 0.011 Θ ≤ 0.000085643377 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12838 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035614550053 : ℝ) * 0.525 / ((1 - 0.011) * 12838) := by gcongr
      _ ≤ (0.000085643377 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12838 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12838 0.011 Θ) :=
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
    badAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12838 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12838 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12838 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12838 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12838 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12838 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12838 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12838 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12838 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12838 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035614550053 : ℝ) * 12838 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003394011910 + 0.003257033411 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12838

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12838
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12838 BstLean.Part154.csC) (piBar (rhoBar 12838 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12838 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12838 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12838 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12838 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12838 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12838 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12838 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12838 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12838 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12838 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052198414308 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12838) ≤ 0.010540034880 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12838 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035614550053)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010540034880 + 2 * 0.737676 / 12838) := by gcongr
    _ ≤ (0.052198414308 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12838 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12838

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12838
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509741976 : ℝ) ≤ plow 12838 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12838) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610554451)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365022661) : eMP 12838 0.011 xi bn ≤ 0.001175343823 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12838 : ℝ) * (1 - 0.011))) ≤ 0.000581163138 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001365022661 / (12838 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581163138 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581163138 : ℝ) + 3.141593 * 0.052610554451 / (12838 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175343823 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610554451)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365022661) : PiBarMP 12838 12 0.011 xi bn ≤ 0.160373270430 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12838 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036946213081 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.679998225062 : ℝ) ≤ √((12838 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.304898393670 : ℝ) ≤ √(12838 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12838) ≤ 0.122963865290 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036946213081 + 0.052610554451 * 1.772454 / (2 * (112.679998225062 : ℝ))) * (1 + 0.001175343823) +
        8 / (12838 * 113.304898393670) + 0.122963865290 := by gcongr
    _ ≤ (0.160373270430 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610554451)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365022661) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281568321775) :
    parallelOracle 12838 0.011 xi bn cd ≤ 0.161352956250 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12838 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12838 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509741976 : ℝ) ≤ plow 12838 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.304898393670 : ℝ) ≤ √(12838 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281568321775 : ℝ) / (2 * 0.560509741976 * 113.304898393670)) * 0.160373270430 +
        0.281568321775 ^ 2 / (2 * 0.560509741976 * 113.304898393670) := by gcongr
    _ ≤ (0.161352956250 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610554451) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001365022661)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281568321775) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12838 12838 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509741976 : ℝ) ≤ plow 12838 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.304898393670 : ℝ) ≤ √(12838 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12838 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12838 Θ 1.22 ≤ 0.011703823214 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.304898393670 := by gcongr <;> linarith
      _ ≤ (0.011703823214 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12838 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12838 12838 0.011 ≤ 0.008436413634 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12838 12838 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12838 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12838 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12838 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12838 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161352956250 + 0.011703823214 + (0.008436413634 : ℝ) *
        (1 + 2 * (0.281568321775 + 0.011703823214) / (0.560509741976 * 113.304898393670))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12838]

end BstLean.Part269.N12838

/-! The original eight local profiles supply actual 12838 moment certificates. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12838 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052610554451 ∧
    0 ≤ bN 12838 BstLean.Part154.csC (groupTheta g) ∧ bN 12838 BstLean.Part154.csC (groupTheta g) ≤ 0.001365022661 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12838 12838 0.011
      (momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12838 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12838 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12838 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229369907467 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12838 0.011
      (momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12838 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12838
/-! The actual computed-centre upper energy formula at 12838. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12838

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12838)
open BstLean.Part268 (cell12838)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085097668605
  | 2 => 0.086033423520
  | 3 => 0.086966333371
  | 4 => 0.087897586953
  | 5 => 0.088828629334
  | 6 => 0.089761200829
  | 7 => 0.090697379818
  | 8 => 0.091639629463
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12838 12838 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12838 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12838

/-! Actual upper energy certificates on all 43 source endpoints at 12838. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12838)
open BstLean.Part268 (cell12838)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12838 (gMinus 12838) (1 - (cell12838 i).lower) ≤ 1 ∧
    energyUpper 12838 (gMinus 12838) (BstLean.Part211.gPlus 12838)
      (finiteEnergy 12838 12838 0.011) (1 - (cell12838 i).lower) ≤
      (cell12838 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨10,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨11,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨12,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨13,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨14,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨15,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨16,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨17,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨18,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨19,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨20,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨21,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨22,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨23,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨24,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨25,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨26,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨27,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨28,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨29,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨30,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨31,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨32,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨33,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨34,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨35,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨36,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨37,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨38,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨39,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨40,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨41,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨42,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨43,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨44,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨45,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨46,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨47,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨48,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨49,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨50,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨51,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12838) (by norm_num)
        (q := 1 - (cell12838 ⟨52,by decide⟩).lower)
        (by norm_num [cell12838]) (by norm_num [cell12838])
      exact ⟨E.1,E.2.trans (by norm_num [cell12838])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12838

/-! Source-cell containment and simple scalar guards at 12838. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12838)
open BstLean.Part268 (cell12838)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12838 ⟨10,by decide⟩).lower ∧ (cell12838 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12838 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12838 ⟨11,by decide⟩).lower ∧ (cell12838 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12838 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12838 ⟨12,by decide⟩).lower ∧ (cell12838 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12838 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12838 ⟨13,by decide⟩).lower ∧ (cell12838 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12838 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12838 ⟨14,by decide⟩).lower ∧ (cell12838 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12838 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12838 ⟨15,by decide⟩).lower ∧ (cell12838 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12838 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12838 ⟨16,by decide⟩).lower ∧ (cell12838 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12838 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12838 ⟨17,by decide⟩).lower ∧ (cell12838 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12838 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12838 ⟨18,by decide⟩).lower ∧ (cell12838 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12838 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12838 ⟨19,by decide⟩).lower ∧ (cell12838 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12838 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12838 ⟨20,by decide⟩).lower ∧ (cell12838 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12838 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12838 ⟨21,by decide⟩).lower ∧ (cell12838 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12838 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12838 ⟨22,by decide⟩).lower ∧ (cell12838 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12838 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12838 ⟨23,by decide⟩).lower ∧ (cell12838 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12838 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12838 ⟨24,by decide⟩).lower ∧ (cell12838 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12838 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12838 ⟨25,by decide⟩).lower ∧ (cell12838 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12838 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12838 ⟨26,by decide⟩).lower ∧ (cell12838 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12838 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12838 ⟨27,by decide⟩).lower ∧ (cell12838 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12838 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12838 ⟨28,by decide⟩).lower ∧ (cell12838 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12838 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12838 ⟨29,by decide⟩).lower ∧ (cell12838 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12838 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12838 ⟨30,by decide⟩).lower ∧ (cell12838 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12838 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12838 ⟨31,by decide⟩).lower ∧ (cell12838 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12838 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12838 ⟨32,by decide⟩).lower ∧ (cell12838 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12838 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12838 ⟨33,by decide⟩).lower ∧ (cell12838 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12838 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12838 ⟨34,by decide⟩).lower ∧ (cell12838 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12838 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12838 ⟨35,by decide⟩).lower ∧ (cell12838 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12838 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12838 ⟨36,by decide⟩).lower ∧ (cell12838 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12838 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12838 ⟨37,by decide⟩).lower ∧ (cell12838 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12838 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12838 ⟨38,by decide⟩).lower ∧ (cell12838 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12838 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12838 ⟨39,by decide⟩).lower ∧ (cell12838 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12838 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12838 ⟨40,by decide⟩).lower ∧ (cell12838 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12838 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12838 ⟨41,by decide⟩).lower ∧ (cell12838 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12838 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12838 ⟨42,by decide⟩).lower ∧ (cell12838 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12838 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12838 ⟨43,by decide⟩).lower ∧ (cell12838 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12838 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12838 ⟨44,by decide⟩).lower ∧ (cell12838 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12838 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12838 ⟨45,by decide⟩).lower ∧ (cell12838 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12838 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12838 ⟨46,by decide⟩).lower ∧ (cell12838 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12838 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12838 ⟨47,by decide⟩).lower ∧ (cell12838 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12838 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12838 ⟨48,by decide⟩).lower ∧ (cell12838 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12838 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12838 ⟨49,by decide⟩).lower ∧ (cell12838 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12838 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12838 ⟨50,by decide⟩).lower ∧ (cell12838 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12838 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12838 ⟨51,by decide⟩).lower ∧ (cell12838 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12838 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12838 ⟨52,by decide⟩).lower ∧ (cell12838 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12838 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12838 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12838 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12838,cell12838,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12838 i).lower ∧
    (cell12838 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12838 i).upper ≤ (0.532 : ℝ) ∧
    (cell12838 i).centre ≤ (0.1 : ℝ) ∧ (cell12838 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12838 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12838 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12838

/-! The local source numeric instances at 12838 have no network premises. -/
namespace BstLean.Part269.N12838
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12838)
open BstLean.Part268 (cell12838)

noncomputable def sourceNumerics12838 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12838 (cell12838 i)
      scalarRow12838.M scalarRow12838.H scalarRow12838.xi := by
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
    energy_allowance := scalarRow12838.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12838]
    centre_nonneg := (scalarRow12838.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12838])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12838
/-! Actual 12839 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12839 ≤ (1.035613150925 : ℝ) := by
  have hr : (113.309311179620 : ℝ) ≤ √(12839 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.309311179620 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12839 12839 (11 / 1000) ≤
    (0.008436085079 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12839) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.309311179620 : ℝ) ≤ √(12839 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12839)
  have hdiv : K / √(12839 : ℝ) ≤ K / 113.309311179620 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.309311179620 ≤ (0.008436085079 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12839.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12839 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12839 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12839 := gPlus_lower 12839
end BstLean.Part269.N12839

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12839
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035613150924 : ℝ) ≤ wn 12839 := by
  have hn : √(12839 : ℝ) ≤ 113.309311179621 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12839 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.309311179621 ≤ 2 / √(12839 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249106746 : ℝ) ≤ rhoBar 12839 BstLean.Part154.csC ∧
    rhoBar 12839 BstLean.Part154.csC ≤ 0.000249107132 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035613150924 : ℝ) / (1.295212 * 12839) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035613150925 : ℝ) / (1.29521 * 12839) := by gcongr
      _ ≤ (0.000249107132 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12839 BstLean.Part154.csC) ≤ 0.000996490583 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12839 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) ≤ 0.000190269610 ∧
    cc1 (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) ≤ 0.000121069837 ∧
    cc2 (rhoBar 12839 BstLean.Part154.csC) ≤ 0.000070281992 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12839 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12839 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12839 BstLean.Part154.csC * nuR (rhoBar 12839 BstLean.Part154.csC)) ≤ 0.000498229778 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249107132 : ℝ) * 0.000996490583 := by gcongr
      _ ≤ (0.000498229778 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12839 BstLean.Part154.csC) * nuR (rhoBar 12839 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996490583 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12839 BstLean.Part154.csC) * rhoBar 12839 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249107132 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249107132 / 2 + 0.399 * 0.000996490583 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190269610 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498229778 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121069837 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249107132 / 1.414213562 := by gcongr
      _ ≤ (0.000070281992 : ℝ) := by norm_num

end BstLean.Part269.N12839

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12839
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) ≤ 1.56342E-7 := by
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12839 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12839 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12839 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190269610 : ℝ) ^ 2 + 0.000121069837 ^ 2 + 3 * 0.000070281992 ^ 2 +
        2 * 0.797885 * 0.000190269610 * 0.000121069837 + 2 * 0.000190269610 * 0.000070281992 +
        4 * 0.797885 * 0.000121069837 * 0.000070281992 := by gcongr
    _ ≤ (1.56342E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12839 BstLean.Part154.csC Θ ≤ 0.002599846594 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12839 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12839 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12839 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035613150925 * 1.56342E-7 / (0.000249106746 : ℝ) := by gcongr
    _ ≤ 0.002599846594 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12839 BstLean.Part154.csC Θ ≤ 0.002884113346 + 0.000656937303 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12839 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12839 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035613150925 : ℝ) * ((2 * Θ * 0.000249107132 +
        (6863 / 10000) * 0.000249107132 * 12839 * 0.000996490583) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002884113346 + 0.000656937303 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12839 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12839 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12839 0.011 Θ ∧ gammaRatio 12839 0.011 Θ ≤ 0.000085636590 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12839 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035613150925 : ℝ) * 0.525 / ((1 - 0.011) * 12839) := by gcongr
      _ ≤ (0.000085636590 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12839 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12839 0.011 Θ) :=
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
    badAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12839 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12839 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12839 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12839 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12839 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12839 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12839 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12839 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12839 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12839 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035613150925 : ℝ) * 12839 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003393775562 + 0.003256783897 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12839

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12839
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12839 BstLean.Part154.csC) (piBar (rhoBar 12839 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12839 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12839 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12839 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12839 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12839 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12839 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12839 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12839 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12839 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12839 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052196359534 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12839) ≤ 0.010539624402 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12839 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035613150925)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010539624402 + 2 * 0.737676 / 12839) := by gcongr
    _ ≤ (0.052196359534 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12839 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12839

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12839
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509786229 : ℝ) ≤ plow 12839 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12839) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610187108)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364919462) : eMP 12839 0.011 xi bn ≤ 0.001175253514 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12839 : ℝ) * (1 - 0.011))) ≤ 0.000581118536 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364919462 / (12839 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581118536 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581118536 : ℝ) + 3.141593 * 0.052610187108 / (12839 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175253514 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610187108)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364919462) : PiBarMP 12839 12 0.011 xi bn ≤ 0.160367060330 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12839 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036944816443 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.684386673576 : ℝ) ≤ √((12839 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.309311179620 : ℝ) ≤ √(12839 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12839) ≤ 0.122959076512 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036944816443 + 0.052610187108 * 1.772454 / (2 * (112.684386673576 : ℝ))) * (1 + 0.001175253514) +
        8 / (12839 * 113.309311179620) + 0.122959076512 := by gcongr
    _ ≤ (0.160367060330 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610187108)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364919462) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281565466234) :
    parallelOracle 12839 0.011 xi bn cd ≤ 0.161346677888 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12839 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12839 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509786229 : ℝ) ≤ plow 12839 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.309311179620 : ℝ) ≤ √(12839 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281565466234 : ℝ) / (2 * 0.560509786229 * 113.309311179620)) * 0.160367060330 +
        0.281565466234 ^ 2 / (2 * 0.560509786229 * 113.309311179620) := by gcongr
    _ ≤ (0.161346677888 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052610187108) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364919462)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281565466234) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12839 12839 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509786229 : ℝ) ≤ plow 12839 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.309311179620 : ℝ) ≤ √(12839 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12839 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12839 Θ 1.22 ≤ 0.011703367413 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.309311179620 := by gcongr <;> linarith
      _ ≤ (0.011703367413 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12839 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12839 12839 0.011 ≤ 0.008436085079 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12839 12839 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12839 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12839 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12839 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12839 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161346677888 + 0.011703367413 + (0.008436085079 : ℝ) *
        (1 + 2 * (0.281565466234 + 0.011703367413) / (0.560509786229 * 113.309311179620))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12839]

end BstLean.Part269.N12839

/-! The original eight local profiles supply actual 12839 moment certificates. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12839 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052610187108 ∧
    0 ≤ bN 12839 BstLean.Part154.csC (groupTheta g) ∧ bN 12839 BstLean.Part154.csC (groupTheta g) ≤ 0.001364919462 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12839 12839 0.011
      (momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12839 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12839 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12839 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229369106700 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12839 0.011
      (momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12839 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12839
/-! The actual computed-centre upper energy formula at 12839. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12839

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12839)
open BstLean.Part268 (cell12839)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085094892505
  | 2 => 0.086030599483
  | 3 => 0.086963454908
  | 4 => 0.087894646046
  | 5 => 0.088825616160
  | 6 => 0.089758103453
  | 7 => 0.090694183840
  | 8 => 0.091636317632
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12839 12839 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12839 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12839

/-! Actual upper energy certificates on all 43 source endpoints at 12839. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12839)
open BstLean.Part268 (cell12839)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12839 (gMinus 12839) (1 - (cell12839 i).lower) ≤ 1 ∧
    energyUpper 12839 (gMinus 12839) (BstLean.Part211.gPlus 12839)
      (finiteEnergy 12839 12839 0.011) (1 - (cell12839 i).lower) ≤
      (cell12839 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨10,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨11,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨12,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨13,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨14,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨15,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨16,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨17,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨18,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨19,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨20,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨21,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨22,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨23,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨24,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨25,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨26,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨27,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨28,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨29,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨30,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨31,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨32,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨33,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨34,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨35,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨36,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨37,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨38,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨39,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨40,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨41,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨42,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨43,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨44,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨45,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨46,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨47,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨48,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨49,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨50,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨51,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12839) (by norm_num)
        (q := 1 - (cell12839 ⟨52,by decide⟩).lower)
        (by norm_num [cell12839]) (by norm_num [cell12839])
      exact ⟨E.1,E.2.trans (by norm_num [cell12839])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12839

/-! Source-cell containment and simple scalar guards at 12839. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12839)
open BstLean.Part268 (cell12839)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12839 ⟨10,by decide⟩).lower ∧ (cell12839 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12839 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12839 ⟨11,by decide⟩).lower ∧ (cell12839 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12839 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12839 ⟨12,by decide⟩).lower ∧ (cell12839 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12839 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12839 ⟨13,by decide⟩).lower ∧ (cell12839 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12839 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12839 ⟨14,by decide⟩).lower ∧ (cell12839 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12839 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12839 ⟨15,by decide⟩).lower ∧ (cell12839 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12839 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12839 ⟨16,by decide⟩).lower ∧ (cell12839 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12839 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12839 ⟨17,by decide⟩).lower ∧ (cell12839 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12839 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12839 ⟨18,by decide⟩).lower ∧ (cell12839 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12839 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12839 ⟨19,by decide⟩).lower ∧ (cell12839 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12839 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12839 ⟨20,by decide⟩).lower ∧ (cell12839 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12839 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12839 ⟨21,by decide⟩).lower ∧ (cell12839 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12839 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12839 ⟨22,by decide⟩).lower ∧ (cell12839 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12839 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12839 ⟨23,by decide⟩).lower ∧ (cell12839 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12839 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12839 ⟨24,by decide⟩).lower ∧ (cell12839 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12839 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12839 ⟨25,by decide⟩).lower ∧ (cell12839 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12839 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12839 ⟨26,by decide⟩).lower ∧ (cell12839 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12839 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12839 ⟨27,by decide⟩).lower ∧ (cell12839 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12839 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12839 ⟨28,by decide⟩).lower ∧ (cell12839 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12839 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12839 ⟨29,by decide⟩).lower ∧ (cell12839 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12839 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12839 ⟨30,by decide⟩).lower ∧ (cell12839 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12839 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12839 ⟨31,by decide⟩).lower ∧ (cell12839 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12839 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12839 ⟨32,by decide⟩).lower ∧ (cell12839 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12839 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12839 ⟨33,by decide⟩).lower ∧ (cell12839 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12839 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12839 ⟨34,by decide⟩).lower ∧ (cell12839 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12839 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12839 ⟨35,by decide⟩).lower ∧ (cell12839 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12839 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12839 ⟨36,by decide⟩).lower ∧ (cell12839 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12839 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12839 ⟨37,by decide⟩).lower ∧ (cell12839 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12839 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12839 ⟨38,by decide⟩).lower ∧ (cell12839 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12839 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12839 ⟨39,by decide⟩).lower ∧ (cell12839 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12839 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12839 ⟨40,by decide⟩).lower ∧ (cell12839 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12839 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12839 ⟨41,by decide⟩).lower ∧ (cell12839 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12839 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12839 ⟨42,by decide⟩).lower ∧ (cell12839 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12839 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12839 ⟨43,by decide⟩).lower ∧ (cell12839 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12839 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12839 ⟨44,by decide⟩).lower ∧ (cell12839 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12839 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12839 ⟨45,by decide⟩).lower ∧ (cell12839 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12839 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12839 ⟨46,by decide⟩).lower ∧ (cell12839 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12839 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12839 ⟨47,by decide⟩).lower ∧ (cell12839 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12839 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12839 ⟨48,by decide⟩).lower ∧ (cell12839 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12839 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12839 ⟨49,by decide⟩).lower ∧ (cell12839 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12839 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12839 ⟨50,by decide⟩).lower ∧ (cell12839 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12839 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12839 ⟨51,by decide⟩).lower ∧ (cell12839 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12839 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12839 ⟨52,by decide⟩).lower ∧ (cell12839 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12839 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12839 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12839 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12839,cell12839,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12839 i).lower ∧
    (cell12839 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12839 i).upper ≤ (0.532 : ℝ) ∧
    (cell12839 i).centre ≤ (0.1 : ℝ) ∧ (cell12839 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12839 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12839 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12839

/-! The local source numeric instances at 12839 have no network premises. -/
namespace BstLean.Part269.N12839
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12839)
open BstLean.Part268 (cell12839)

noncomputable def sourceNumerics12839 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12839 (cell12839 i)
      scalarRow12839.M scalarRow12839.H scalarRow12839.xi := by
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
    energy_allowance := scalarRow12839.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12839]
    centre_nonneg := (scalarRow12839.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12839])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12839
/-! Actual 12840 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12840 ≤ (1.035611751961 : ℝ) := by
  have hr : (113.313723793722 : ℝ) ≤ √(12840 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.313723793722 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12840 12840 (11 / 1000) ≤
    (0.008435756562 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12840) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.313723793722 : ℝ) ≤ √(12840 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12840)
  have hdiv : K / √(12840 : ℝ) ≤ K / 113.313723793722 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.313723793722 ≤ (0.008435756562 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12840.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12840 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12840 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12840 := gPlus_lower 12840
end BstLean.Part269.N12840

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12840
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035611751960 : ℝ) ≤ wn 12840 := by
  have hn : √(12840 : ℝ) ≤ 113.313723793723 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12840 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.313723793723 ≤ 2 / √(12840 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249087009 : ℝ) ≤ rhoBar 12840 BstLean.Part154.csC ∧
    rhoBar 12840 BstLean.Part154.csC ≤ 0.000249087394 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035611751960 : ℝ) / (1.295212 * 12840) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035611751961 : ℝ) / (1.29521 * 12840) := by gcongr
      _ ≤ (0.000249087394 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12840 BstLean.Part154.csC) ≤ 0.000996411621 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12840 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) ≤ 0.000190254534 ∧
    cc1 (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) ≤ 0.000121060243 ∧
    cc2 (rhoBar 12840 BstLean.Part154.csC) ≤ 0.000070276423 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12840 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12840 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12840 BstLean.Part154.csC * nuR (rhoBar 12840 BstLean.Part154.csC)) ≤ 0.000498190300 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249087394 : ℝ) * 0.000996411621 := by gcongr
      _ ≤ (0.000498190300 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12840 BstLean.Part154.csC) * nuR (rhoBar 12840 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996411621 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12840 BstLean.Part154.csC) * rhoBar 12840 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249087394 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249087394 / 2 + 0.399 * 0.000996411621 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190254534 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498190300 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121060243 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249087394 / 1.414213562 := by gcongr
      _ ≤ (0.000070276423 : ℝ) := by norm_num

end BstLean.Part269.N12840

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12840
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) ≤ 1.56317E-7 := by
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12840 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12840 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12840 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190254534 : ℝ) ^ 2 + 0.000121060243 ^ 2 + 3 * 0.000070276423 ^ 2 +
        2 * 0.797885 * 0.000190254534 * 0.000121060243 + 2 * 0.000190254534 * 0.000070276423 +
        4 * 0.797885 * 0.000121060243 * 0.000070276423 := by gcongr
    _ ≤ (1.56317E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12840 BstLean.Part154.csC Θ ≤ 0.002599633324 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12840 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12840 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12840 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035611751961 * 1.56317E-7 / (0.000249087009 : ℝ) := by gcongr
    _ ≤ 0.002599633324 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12840 BstLean.Part154.csC Θ ≤ 0.002883877009 + 0.000656884364 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12840 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12840 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035611751961 : ℝ) * ((2 * Θ * 0.000249087394 +
        (6863 / 10000) * 0.000249087394 * 12840 * 0.000996411621) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002883877009 + 0.000656884364 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12840 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12840 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12840 0.011 Θ ∧ gammaRatio 12840 0.011 Θ ≤ 0.000085629805 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12840 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035611751961 : ℝ) * 0.525 / ((1 - 0.011) * 12840) := by gcongr
      _ ≤ (0.000085629805 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12840 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12840 0.011 Θ) :=
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
    badAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12840 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12840 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12840 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12840 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12840 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12840 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12840 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12840 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12840 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12840 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035611751961 : ℝ) * 12840 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003393539225 + 0.003256517688 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12840

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12840
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12840 BstLean.Part154.csC) (piBar (rhoBar 12840 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12840 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12840 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12840 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12840 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12840 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12840 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12840 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12840 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12840 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12840 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052194305007 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12840) ≤ 0.010539213973 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12840 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035611751961)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010539213973 + 2 * 0.737676 / 12840) := by gcongr
    _ ≤ (0.052194305007 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12840 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12840

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12840
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509830475 : ℝ) ≤ plow 12840 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12840) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609811012)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364807496) : eMP 12840 0.011 xi bn ≤ 0.001175159479 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12840 : ℝ) * (1 - 0.011))) ≤ 0.000581072072 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364807496 / (12840 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581072072 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581072072 : ℝ) + 3.141593 * 0.052609811012 / (12840 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175159479 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609811012)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364807496) : PiBarMP 12840 12 0.011 xi bn ≤ 0.160360731736 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12840 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036943301098 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.688774951190 : ℝ) ≤ √((12840 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.313723793722 : ℝ) ≤ √(12840 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12840) ≤ 0.122954288292 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036943301098 + 0.052609811012 * 1.772454 / (2 * (112.688774951190 : ℝ))) * (1 + 0.001175159479) +
        8 / (12840 * 113.313723793722) + 0.122954288292 := by gcongr
    _ ≤ (0.160360731736 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609811012)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364807496) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281562591856) :
    parallelOracle 12840 0.011 xi bn cd ≤ 0.161340280670 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12840 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12840 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509830475 : ℝ) ≤ plow 12840 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.313723793722 : ℝ) ≤ √(12840 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281562591856 : ℝ) / (2 * 0.560509830475 * 113.313723793722)) * 0.160360731736 +
        0.281562591856 ^ 2 / (2 * 0.560509830475 * 113.313723793722) := by gcongr
    _ ≤ (0.161340280670 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609811012) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364807496)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281562591856) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12840 12840 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509830475 : ℝ) ≤ plow 12840 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.313723793722 : ℝ) ≤ √(12840 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12840 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12840 Θ 1.22 ≤ 0.011702911666 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.313723793722 := by gcongr <;> linarith
      _ ≤ (0.011702911666 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12840 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12840 12840 0.011 ≤ 0.008435756562 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12840 12840 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12840 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12840 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12840 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12840 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161340280670 + 0.011702911666 + (0.008435756562 : ℝ) *
        (1 + 2 * (0.281562591856 + 0.011702911666) / (0.560509830475 * 113.313723793722))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12840]

end BstLean.Part269.N12840

/-! The original eight local profiles supply actual 12840 moment certificates. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12840 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052609811012 ∧
    0 ≤ bN 12840 BstLean.Part154.csC (groupTheta g) ∧ bN 12840 BstLean.Part154.csC (groupTheta g) ≤ 0.001364807496 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12840 12840 0.011
      (momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12840 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12840 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12840 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229368286849 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12840 0.011
      (momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12840 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12840
/-! The actual computed-centre upper energy formula at 12840. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12840

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12840)
open BstLean.Part268 (cell12840)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085092117350
  | 2 => 0.086027776428
  | 3 => 0.086960577472
  | 4 => 0.087891706222
  | 5 => 0.088822604140
  | 6 => 0.089755007315
  | 7 => 0.090690989202
  | 8 => 0.091633007263
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12840 12840 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12840 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12840

/-! Actual upper energy certificates on all 43 source endpoints at 12840. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12840)
open BstLean.Part268 (cell12840)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12840 (gMinus 12840) (1 - (cell12840 i).lower) ≤ 1 ∧
    energyUpper 12840 (gMinus 12840) (BstLean.Part211.gPlus 12840)
      (finiteEnergy 12840 12840 0.011) (1 - (cell12840 i).lower) ≤
      (cell12840 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨10,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨11,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨12,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨13,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨14,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨15,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨16,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨17,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨18,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨19,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨20,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨21,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨22,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨23,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨24,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨25,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨26,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨27,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨28,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨29,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨30,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨31,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨32,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨33,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨34,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨35,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨36,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨37,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨38,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨39,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨40,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨41,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨42,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨43,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨44,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨45,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨46,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨47,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨48,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨49,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨50,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨51,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12840) (by norm_num)
        (q := 1 - (cell12840 ⟨52,by decide⟩).lower)
        (by norm_num [cell12840]) (by norm_num [cell12840])
      exact ⟨E.1,E.2.trans (by norm_num [cell12840])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12840

/-! Source-cell containment and simple scalar guards at 12840. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12840)
open BstLean.Part268 (cell12840)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12840 ⟨10,by decide⟩).lower ∧ (cell12840 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12840 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12840 ⟨11,by decide⟩).lower ∧ (cell12840 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12840 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12840 ⟨12,by decide⟩).lower ∧ (cell12840 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12840 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12840 ⟨13,by decide⟩).lower ∧ (cell12840 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12840 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12840 ⟨14,by decide⟩).lower ∧ (cell12840 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12840 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12840 ⟨15,by decide⟩).lower ∧ (cell12840 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12840 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12840 ⟨16,by decide⟩).lower ∧ (cell12840 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12840 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12840 ⟨17,by decide⟩).lower ∧ (cell12840 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12840 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12840 ⟨18,by decide⟩).lower ∧ (cell12840 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12840 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12840 ⟨19,by decide⟩).lower ∧ (cell12840 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12840 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12840 ⟨20,by decide⟩).lower ∧ (cell12840 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12840 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12840 ⟨21,by decide⟩).lower ∧ (cell12840 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12840 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12840 ⟨22,by decide⟩).lower ∧ (cell12840 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12840 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12840 ⟨23,by decide⟩).lower ∧ (cell12840 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12840 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12840 ⟨24,by decide⟩).lower ∧ (cell12840 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12840 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12840 ⟨25,by decide⟩).lower ∧ (cell12840 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12840 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12840 ⟨26,by decide⟩).lower ∧ (cell12840 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12840 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12840 ⟨27,by decide⟩).lower ∧ (cell12840 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12840 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12840 ⟨28,by decide⟩).lower ∧ (cell12840 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12840 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12840 ⟨29,by decide⟩).lower ∧ (cell12840 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12840 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12840 ⟨30,by decide⟩).lower ∧ (cell12840 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12840 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12840 ⟨31,by decide⟩).lower ∧ (cell12840 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12840 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12840 ⟨32,by decide⟩).lower ∧ (cell12840 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12840 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12840 ⟨33,by decide⟩).lower ∧ (cell12840 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12840 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12840 ⟨34,by decide⟩).lower ∧ (cell12840 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12840 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12840 ⟨35,by decide⟩).lower ∧ (cell12840 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12840 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12840 ⟨36,by decide⟩).lower ∧ (cell12840 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12840 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12840 ⟨37,by decide⟩).lower ∧ (cell12840 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12840 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12840 ⟨38,by decide⟩).lower ∧ (cell12840 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12840 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12840 ⟨39,by decide⟩).lower ∧ (cell12840 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12840 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12840 ⟨40,by decide⟩).lower ∧ (cell12840 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12840 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12840 ⟨41,by decide⟩).lower ∧ (cell12840 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12840 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12840 ⟨42,by decide⟩).lower ∧ (cell12840 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12840 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12840 ⟨43,by decide⟩).lower ∧ (cell12840 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12840 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12840 ⟨44,by decide⟩).lower ∧ (cell12840 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12840 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12840 ⟨45,by decide⟩).lower ∧ (cell12840 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12840 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12840 ⟨46,by decide⟩).lower ∧ (cell12840 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12840 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12840 ⟨47,by decide⟩).lower ∧ (cell12840 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12840 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12840 ⟨48,by decide⟩).lower ∧ (cell12840 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12840 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12840 ⟨49,by decide⟩).lower ∧ (cell12840 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12840 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12840 ⟨50,by decide⟩).lower ∧ (cell12840 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12840 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12840 ⟨51,by decide⟩).lower ∧ (cell12840 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12840 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12840 ⟨52,by decide⟩).lower ∧ (cell12840 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12840 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12840 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12840 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12840,cell12840,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12840 i).lower ∧
    (cell12840 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12840 i).upper ≤ (0.532 : ℝ) ∧
    (cell12840 i).centre ≤ (0.1 : ℝ) ∧ (cell12840 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12840 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12840 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12840

/-! The local source numeric instances at 12840 have no network premises. -/
namespace BstLean.Part269.N12840
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12840)
open BstLean.Part268 (cell12840)

noncomputable def sourceNumerics12840 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12840 (cell12840 i)
      scalarRow12840.M scalarRow12840.H scalarRow12840.xi := by
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
    energy_allowance := scalarRow12840.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12840]
    centre_nonneg := (scalarRow12840.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12840])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12840
/-! Actual 12841 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12841 ≤ (1.035610353162 : ℝ) := by
  have hr : (113.318136235997 : ℝ) ≤ √(12841 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.318136235997 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12841 12841 (11 / 1000) ≤
    (0.008435428083 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12841) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.318136235997 : ℝ) ≤ √(12841 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12841)
  have hdiv : K / √(12841 : ℝ) ≤ K / 113.318136235997 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.318136235997 ≤ (0.008435428083 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12841.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12841 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12841 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12841 := gPlus_lower 12841
end BstLean.Part269.N12841

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12841
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035610353161 : ℝ) ≤ wn 12841 := by
  have hn : √(12841 : ℝ) ≤ 113.318136235998 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12841 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.318136235998 ≤ 2 / √(12841 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249067275 : ℝ) ≤ rhoBar 12841 BstLean.Part154.csC ∧
    rhoBar 12841 BstLean.Part154.csC ≤ 0.000249067660 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035610353161 : ℝ) / (1.295212 * 12841) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035610353162 : ℝ) / (1.29521 * 12841) := by gcongr
      _ ≤ (0.000249067660 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12841 BstLean.Part154.csC) ≤ 0.000996332675 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12841 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) ≤ 0.000190239460 ∧
    cc1 (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) ≤ 0.000121050652 ∧
    cc2 (rhoBar 12841 BstLean.Part154.csC) ≤ 0.000070270856 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12841 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12841 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12841 BstLean.Part154.csC * nuR (rhoBar 12841 BstLean.Part154.csC)) ≤ 0.000498150829 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249067660 : ℝ) * 0.000996332675 := by gcongr
      _ ≤ (0.000498150829 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12841 BstLean.Part154.csC) * nuR (rhoBar 12841 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996332675 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12841 BstLean.Part154.csC) * rhoBar 12841 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249067660 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249067660 / 2 + 0.399 * 0.000996332675 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190239460 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498150829 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121050652 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249067660 / 1.414213562 := by gcongr
      _ ≤ (0.000070270856 : ℝ) := by norm_num

end BstLean.Part269.N12841

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12841
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) ≤ 1.56292E-7 := by
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12841 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12841 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12841 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190239460 : ℝ) ^ 2 + 0.000121050652 ^ 2 + 3 * 0.000070270856 ^ 2 +
        2 * 0.797885 * 0.000190239460 * 0.000121050652 + 2 * 0.000190239460 * 0.000070270856 +
        4 * 0.797885 * 0.000121050652 * 0.000070270856 := by gcongr
    _ ≤ (1.56292E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12841 BstLean.Part154.csC Θ ≤ 0.002599419990 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12841 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12841 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12841 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035610353162 * 1.56292E-7 / (0.000249067275 : ℝ) := by gcongr
    _ ≤ 0.002599419990 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12841 BstLean.Part154.csC Θ ≤ 0.002883640732 + 0.000656831435 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12841 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12841 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035610353162 : ℝ) * ((2 * Θ * 0.000249067660 +
        (6863 / 10000) * 0.000249067660 * 12841 * 0.000996332675) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002883640732 + 0.000656831435 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12841 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12841 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12841 0.011 Θ ∧ gammaRatio 12841 0.011 Θ ≤ 0.000085623021 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12841 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035610353162 : ℝ) * 0.525 / ((1 - 0.011) * 12841) := by gcongr
      _ ≤ (0.000085623021 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12841 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12841 0.011 Θ) :=
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
    badAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12841 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12841 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12841 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12841 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12841 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12841 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12841 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12841 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12841 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12841 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035610353162 : ℝ) * 12841 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003393302948 + 0.003256251425 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12841

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12841
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12841 BstLean.Part154.csC) (piBar (rhoBar 12841 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12841 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12841 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12841 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12841 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12841 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12841 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12841 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12841 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12841 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12841 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052192250718 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12841) ≤ 0.010538803591 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12841 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035610353162)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010538803591 + 2 * 0.737676 / 12841) := by gcongr
    _ ≤ (0.052192250718 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12841 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12841

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12841
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509874713 : ℝ) ≤ plow 12841 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12841) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609434947)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364695495) : eMP 12841 0.011 xi bn ≤ 0.001175065437 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12841 : ℝ) * (1 - 0.011))) ≤ 0.000581025604 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364695495 / (12841 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581025604 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581025604 : ℝ) + 3.141593 * 0.052609434947 / (12841 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001175065437 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609434947)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364695495) : PiBarMP 12841 12 0.011 xi bn ≤ 0.160354403168 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12841 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036941785217 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.693163057924 : ℝ) ≤ √((12841 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.318136235997 : ℝ) ≤ √(12841 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12841) ≤ 0.122949500632 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036941785217 + 0.052609434947 * 1.772454 / (2 * (112.693163057924 : ℝ))) * (1 + 0.001175065437) +
        8 / (12841 * 113.318136235997) + 0.122949500632 := by gcongr
    _ ≤ (0.160354403168 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609434947)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364695495) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281559717782) :
    parallelOracle 12841 0.011 xi bn cd ≤ 0.161333883487 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12841 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12841 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509874713 : ℝ) ≤ plow 12841 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.318136235997 : ℝ) ≤ √(12841 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281559717782 : ℝ) / (2 * 0.560509874713 * 113.318136235997)) * 0.160354403168 +
        0.281559717782 ^ 2 / (2 * 0.560509874713 * 113.318136235997) := by gcongr
    _ ≤ (0.161333883487 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609434947) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364695495)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281559717782) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12841 12841 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509874713 : ℝ) ≤ plow 12841 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.318136235997 : ℝ) ≤ √(12841 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12841 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12841 Θ 1.22 ≤ 0.011702455971 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.318136235997 := by gcongr <;> linarith
      _ ≤ (0.011702455971 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12841 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12841 12841 0.011 ≤ 0.008435428083 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12841 12841 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12841 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12841 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12841 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12841 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161333883487 + 0.011702455971 + (0.008435428083 : ℝ) *
        (1 + 2 * (0.281559717782 + 0.011702455971) / (0.560509874713 * 113.318136235997))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12841]

end BstLean.Part269.N12841

/-! The original eight local profiles supply actual 12841 moment certificates. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12841 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052609434947 ∧
    0 ≤ bN 12841 BstLean.Part154.csC (groupTheta g) ∧ bN 12841 BstLean.Part154.csC (groupTheta g) ≤ 0.001364695495 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12841 12841 0.011
      (momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12841 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12841 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12841 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229367467064 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12841 0.011
      (momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12841 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12841
/-! The actual computed-centre upper energy formula at 12841. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12841

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12841)
open BstLean.Part268 (cell12841)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085089343138
  | 2 => 0.086024954353
  | 3 => 0.086957701062
  | 4 => 0.087888767481
  | 5 => 0.088819593271
  | 6 => 0.089751912412
  | 7 => 0.090687795901
  | 8 => 0.091629698355
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12841 12841 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12841 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12841

/-! Actual upper energy certificates on all 43 source endpoints at 12841. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12841)
open BstLean.Part268 (cell12841)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12841 (gMinus 12841) (1 - (cell12841 i).lower) ≤ 1 ∧
    energyUpper 12841 (gMinus 12841) (BstLean.Part211.gPlus 12841)
      (finiteEnergy 12841 12841 0.011) (1 - (cell12841 i).lower) ≤
      (cell12841 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨10,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨11,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨12,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨13,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨14,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨15,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨16,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨17,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨18,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨19,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨20,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨21,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨22,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨23,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨24,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨25,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨26,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨27,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨28,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨29,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨30,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨31,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨32,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨33,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨34,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨35,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨36,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨37,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨38,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨39,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨40,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨41,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨42,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨43,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨44,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨45,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨46,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨47,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨48,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨49,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨50,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨51,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12841) (by norm_num)
        (q := 1 - (cell12841 ⟨52,by decide⟩).lower)
        (by norm_num [cell12841]) (by norm_num [cell12841])
      exact ⟨E.1,E.2.trans (by norm_num [cell12841])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12841

/-! Source-cell containment and simple scalar guards at 12841. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12841)
open BstLean.Part268 (cell12841)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12841 ⟨10,by decide⟩).lower ∧ (cell12841 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12841 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12841 ⟨11,by decide⟩).lower ∧ (cell12841 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12841 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12841 ⟨12,by decide⟩).lower ∧ (cell12841 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12841 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12841 ⟨13,by decide⟩).lower ∧ (cell12841 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12841 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12841 ⟨14,by decide⟩).lower ∧ (cell12841 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12841 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12841 ⟨15,by decide⟩).lower ∧ (cell12841 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12841 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12841 ⟨16,by decide⟩).lower ∧ (cell12841 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12841 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12841 ⟨17,by decide⟩).lower ∧ (cell12841 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12841 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12841 ⟨18,by decide⟩).lower ∧ (cell12841 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12841 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12841 ⟨19,by decide⟩).lower ∧ (cell12841 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12841 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12841 ⟨20,by decide⟩).lower ∧ (cell12841 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12841 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12841 ⟨21,by decide⟩).lower ∧ (cell12841 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12841 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12841 ⟨22,by decide⟩).lower ∧ (cell12841 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12841 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12841 ⟨23,by decide⟩).lower ∧ (cell12841 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12841 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12841 ⟨24,by decide⟩).lower ∧ (cell12841 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12841 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12841 ⟨25,by decide⟩).lower ∧ (cell12841 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12841 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12841 ⟨26,by decide⟩).lower ∧ (cell12841 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12841 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12841 ⟨27,by decide⟩).lower ∧ (cell12841 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12841 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12841 ⟨28,by decide⟩).lower ∧ (cell12841 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12841 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12841 ⟨29,by decide⟩).lower ∧ (cell12841 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12841 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12841 ⟨30,by decide⟩).lower ∧ (cell12841 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12841 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12841 ⟨31,by decide⟩).lower ∧ (cell12841 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12841 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12841 ⟨32,by decide⟩).lower ∧ (cell12841 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12841 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12841 ⟨33,by decide⟩).lower ∧ (cell12841 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12841 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12841 ⟨34,by decide⟩).lower ∧ (cell12841 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12841 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12841 ⟨35,by decide⟩).lower ∧ (cell12841 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12841 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12841 ⟨36,by decide⟩).lower ∧ (cell12841 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12841 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12841 ⟨37,by decide⟩).lower ∧ (cell12841 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12841 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12841 ⟨38,by decide⟩).lower ∧ (cell12841 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12841 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12841 ⟨39,by decide⟩).lower ∧ (cell12841 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12841 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12841 ⟨40,by decide⟩).lower ∧ (cell12841 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12841 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12841 ⟨41,by decide⟩).lower ∧ (cell12841 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12841 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12841 ⟨42,by decide⟩).lower ∧ (cell12841 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12841 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12841 ⟨43,by decide⟩).lower ∧ (cell12841 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12841 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12841 ⟨44,by decide⟩).lower ∧ (cell12841 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12841 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12841 ⟨45,by decide⟩).lower ∧ (cell12841 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12841 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12841 ⟨46,by decide⟩).lower ∧ (cell12841 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12841 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12841 ⟨47,by decide⟩).lower ∧ (cell12841 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12841 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12841 ⟨48,by decide⟩).lower ∧ (cell12841 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12841 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12841 ⟨49,by decide⟩).lower ∧ (cell12841 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12841 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12841 ⟨50,by decide⟩).lower ∧ (cell12841 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12841 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12841 ⟨51,by decide⟩).lower ∧ (cell12841 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12841 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12841 ⟨52,by decide⟩).lower ∧ (cell12841 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12841 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12841 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12841 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12841,cell12841,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12841 i).lower ∧
    (cell12841 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12841 i).upper ≤ (0.532 : ℝ) ∧
    (cell12841 i).centre ≤ (0.1 : ℝ) ∧ (cell12841 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12841 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12841 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12841

/-! The local source numeric instances at 12841 have no network premises. -/
namespace BstLean.Part269.N12841
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12841)
open BstLean.Part268 (cell12841)

noncomputable def sourceNumerics12841 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12841 (cell12841 i)
      scalarRow12841.M scalarRow12841.H scalarRow12841.xi := by
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
    energy_allowance := scalarRow12841.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12841]
    centre_nonneg := (scalarRow12841.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12841])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12841
/-! Actual 12842 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12842 ≤ (1.035608954527 : ℝ) := by
  have hr : (113.322548506464 : ℝ) ≤ √(12842 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.322548506464 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12842 12842 (11 / 1000) ≤
    (0.008435099643 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12842) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.322548506464 : ℝ) ≤ √(12842 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12842)
  have hdiv : K / √(12842 : ℝ) ≤ K / 113.322548506464 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.322548506464 ≤ (0.008435099643 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12842.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12842 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12842 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12842 := gPlus_lower 12842
end BstLean.Part269.N12842

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12842
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035608954526 : ℝ) ≤ wn 12842 := by
  have hn : √(12842 : ℝ) ≤ 113.322548506465 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12842 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.322548506465 ≤ 2 / √(12842 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249047543 : ℝ) ≤ rhoBar 12842 BstLean.Part154.csC ∧
    rhoBar 12842 BstLean.Part154.csC ≤ 0.000249047929 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035608954526 : ℝ) / (1.295212 * 12842) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035608954527 : ℝ) / (1.29521 * 12842) := by gcongr
      _ ≤ (0.000249047929 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12842 BstLean.Part154.csC) ≤ 0.000996253741 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12842 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) ≤ 0.000190224389 ∧
    cc1 (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) ≤ 0.000121041062 ∧
    cc2 (rhoBar 12842 BstLean.Part154.csC) ≤ 0.000070265289 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12842 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12842 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12842 BstLean.Part154.csC * nuR (rhoBar 12842 BstLean.Part154.csC)) ≤ 0.000498111365 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249047929 : ℝ) * 0.000996253741 := by gcongr
      _ ≤ (0.000498111365 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12842 BstLean.Part154.csC) * nuR (rhoBar 12842 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996253741 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12842 BstLean.Part154.csC) * rhoBar 12842 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249047929 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249047929 / 2 + 0.399 * 0.000996253741 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190224389 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498111365 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121041062 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249047929 / 1.414213562 := by gcongr
      _ ≤ (0.000070265289 : ℝ) := by norm_num

end BstLean.Part269.N12842

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12842
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) ≤ 1.56267E-7 := by
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12842 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12842 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12842 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190224389 : ℝ) ^ 2 + 0.000121041062 ^ 2 + 3 * 0.000070265289 ^ 2 +
        2 * 0.797885 * 0.000190224389 * 0.000121041062 + 2 * 0.000190224389 * 0.000070265289 +
        4 * 0.797885 * 0.000121041062 * 0.000070265289 := by gcongr
    _ ≤ (1.56267E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12842 BstLean.Part154.csC Θ ≤ 0.002599206603 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12842 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12842 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12842 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035608954527 * 1.56267E-7 / (0.000249047543 : ℝ) := by gcongr
    _ ≤ 0.002599206603 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12842 BstLean.Part154.csC Θ ≤ 0.002883404490 + 0.000656778514 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12842 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12842 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035608954527 : ℝ) * ((2 * Θ * 0.000249047929 +
        (6863 / 10000) * 0.000249047929 * 12842 * 0.000996253741) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002883404490 + 0.000656778514 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12842 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12842 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12842 0.011 Θ ∧ gammaRatio 12842 0.011 Θ ≤ 0.000085616238 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12842 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035608954527 : ℝ) * 0.525 / ((1 - 0.011) * 12842) := by gcongr
      _ ≤ (0.000085616238 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12842 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12842 0.011 Θ) :=
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
    badAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12842 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12842 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12842 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12842 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12842 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12842 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12842 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12842 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12842 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12842 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035608954527 : ℝ) * 12842 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003393066706 + 0.003255985117 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12842

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12842
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12842 BstLean.Part154.csC) (piBar (rhoBar 12842 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12842 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12842 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12842 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12842 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12842 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12842 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12842 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12842 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12842 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12842 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052190196675 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12842) ≤ 0.010538393258 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12842 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035608954527)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010538393258 + 2 * 0.737676 / 12842) := by gcongr
    _ ≤ (0.052190196675 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12842 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12842

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12842
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509918945 : ℝ) ≤ plow 12842 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12842) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609058893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364583467) : eMP 12842 0.011 xi bn ≤ 0.001174971390 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12842 : ℝ) * (1 - 0.011))) ≤ 0.000580979134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364583467 / (12842 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580979134 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580979134 : ℝ) + 3.141593 * 0.052609058893 / (12842 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174971390 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609058893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364583467) : PiBarMP 12842 12 0.011 xi bn ≤ 0.160348074735 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12842 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036940268909 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.697550993799 : ℝ) ≤ √((12842 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.322548506464 : ℝ) ≤ √(12842 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12842) ≤ 0.122944713532 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036940268909 + 0.052609058893 * 1.772454 / (2 * (112.697550993799 : ℝ))) * (1 + 0.001174971390) +
        8 / (12842 * 113.322548506464) + 0.122944713532 := by gcongr
    _ ≤ (0.160348074735 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609058893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364583467) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281556843974) :
    parallelOracle 12842 0.011 xi bn cd ≤ 0.161327486448 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12842 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12842 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509918945 : ℝ) ≤ plow 12842 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.322548506464 : ℝ) ≤ √(12842 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281556843974 : ℝ) / (2 * 0.560509918945 * 113.322548506464)) * 0.160348074735 +
        0.281556843974 ^ 2 / (2 * 0.560509918945 * 113.322548506464) := by gcongr
    _ ≤ (0.161327486448 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052609058893) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364583467)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281556843974) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12842 12842 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509918945 : ℝ) ≤ plow 12842 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.322548506464 : ℝ) ≤ √(12842 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12842 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12842 Θ 1.22 ≤ 0.011702000330 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.322548506464 := by gcongr <;> linarith
      _ ≤ (0.011702000330 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12842 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12842 12842 0.011 ≤ 0.008435099643 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12842 12842 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12842 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12842 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12842 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12842 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161327486448 + 0.011702000330 + (0.008435099643 : ℝ) *
        (1 + 2 * (0.281556843974 + 0.011702000330) / (0.560509918945 * 113.322548506464))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12842]

end BstLean.Part269.N12842

/-! The original eight local profiles supply actual 12842 moment certificates. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12842 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052609058893 ∧
    0 ≤ bN 12842 BstLean.Part154.csC (groupTheta g) ∧ bN 12842 BstLean.Part154.csC (groupTheta g) ≤ 0.001364583467 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12842 12842 0.011
      (momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12842 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12842 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12842 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229366647299 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12842 0.011
      (momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12842 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12842
/-! The actual computed-centre upper energy formula at 12842. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12842

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12842)
open BstLean.Part268 (cell12842)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085086569868
  | 2 => 0.086022133258
  | 3 => 0.086954825678
  | 4 => 0.087885829821
  | 5 => 0.088816583552
  | 6 => 0.089748818743
  | 7 => 0.090684603936
  | 8 => 0.091626390905
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12842 12842 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12842 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12842

/-! Actual upper energy certificates on all 43 source endpoints at 12842. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12842)
open BstLean.Part268 (cell12842)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12842 (gMinus 12842) (1 - (cell12842 i).lower) ≤ 1 ∧
    energyUpper 12842 (gMinus 12842) (BstLean.Part211.gPlus 12842)
      (finiteEnergy 12842 12842 0.011) (1 - (cell12842 i).lower) ≤
      (cell12842 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨10,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨11,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨12,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨13,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨14,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨15,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨16,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨17,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨18,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨19,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨20,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨21,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨22,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨23,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨24,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨25,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨26,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨27,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨28,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨29,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨30,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨31,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨32,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨33,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨34,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨35,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨36,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨37,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨38,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨39,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨40,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨41,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨42,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨43,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨44,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨45,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨46,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨47,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨48,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨49,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨50,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨51,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12842) (by norm_num)
        (q := 1 - (cell12842 ⟨52,by decide⟩).lower)
        (by norm_num [cell12842]) (by norm_num [cell12842])
      exact ⟨E.1,E.2.trans (by norm_num [cell12842])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12842

/-! Source-cell containment and simple scalar guards at 12842. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12842)
open BstLean.Part268 (cell12842)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12842 ⟨10,by decide⟩).lower ∧ (cell12842 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12842 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12842 ⟨11,by decide⟩).lower ∧ (cell12842 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12842 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12842 ⟨12,by decide⟩).lower ∧ (cell12842 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12842 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12842 ⟨13,by decide⟩).lower ∧ (cell12842 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12842 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12842 ⟨14,by decide⟩).lower ∧ (cell12842 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12842 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12842 ⟨15,by decide⟩).lower ∧ (cell12842 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12842 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12842 ⟨16,by decide⟩).lower ∧ (cell12842 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12842 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12842 ⟨17,by decide⟩).lower ∧ (cell12842 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12842 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12842 ⟨18,by decide⟩).lower ∧ (cell12842 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12842 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12842 ⟨19,by decide⟩).lower ∧ (cell12842 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12842 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12842 ⟨20,by decide⟩).lower ∧ (cell12842 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12842 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12842 ⟨21,by decide⟩).lower ∧ (cell12842 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12842 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12842 ⟨22,by decide⟩).lower ∧ (cell12842 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12842 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12842 ⟨23,by decide⟩).lower ∧ (cell12842 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12842 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12842 ⟨24,by decide⟩).lower ∧ (cell12842 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12842 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12842 ⟨25,by decide⟩).lower ∧ (cell12842 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12842 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12842 ⟨26,by decide⟩).lower ∧ (cell12842 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12842 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12842 ⟨27,by decide⟩).lower ∧ (cell12842 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12842 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12842 ⟨28,by decide⟩).lower ∧ (cell12842 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12842 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12842 ⟨29,by decide⟩).lower ∧ (cell12842 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12842 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12842 ⟨30,by decide⟩).lower ∧ (cell12842 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12842 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12842 ⟨31,by decide⟩).lower ∧ (cell12842 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12842 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12842 ⟨32,by decide⟩).lower ∧ (cell12842 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12842 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12842 ⟨33,by decide⟩).lower ∧ (cell12842 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12842 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12842 ⟨34,by decide⟩).lower ∧ (cell12842 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12842 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12842 ⟨35,by decide⟩).lower ∧ (cell12842 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12842 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12842 ⟨36,by decide⟩).lower ∧ (cell12842 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12842 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12842 ⟨37,by decide⟩).lower ∧ (cell12842 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12842 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12842 ⟨38,by decide⟩).lower ∧ (cell12842 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12842 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12842 ⟨39,by decide⟩).lower ∧ (cell12842 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12842 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12842 ⟨40,by decide⟩).lower ∧ (cell12842 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12842 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12842 ⟨41,by decide⟩).lower ∧ (cell12842 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12842 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12842 ⟨42,by decide⟩).lower ∧ (cell12842 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12842 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12842 ⟨43,by decide⟩).lower ∧ (cell12842 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12842 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12842 ⟨44,by decide⟩).lower ∧ (cell12842 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12842 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12842 ⟨45,by decide⟩).lower ∧ (cell12842 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12842 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12842 ⟨46,by decide⟩).lower ∧ (cell12842 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12842 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12842 ⟨47,by decide⟩).lower ∧ (cell12842 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12842 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12842 ⟨48,by decide⟩).lower ∧ (cell12842 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12842 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12842 ⟨49,by decide⟩).lower ∧ (cell12842 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12842 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12842 ⟨50,by decide⟩).lower ∧ (cell12842 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12842 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12842 ⟨51,by decide⟩).lower ∧ (cell12842 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12842 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12842 ⟨52,by decide⟩).lower ∧ (cell12842 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12842 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12842 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12842 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12842,cell12842,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12842 i).lower ∧
    (cell12842 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12842 i).upper ≤ (0.532 : ℝ) ∧
    (cell12842 i).centre ≤ (0.1 : ℝ) ∧ (cell12842 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12842 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12842 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12842

/-! The local source numeric instances at 12842 have no network premises. -/
namespace BstLean.Part269.N12842
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12842)
open BstLean.Part268 (cell12842)

noncomputable def sourceNumerics12842 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12842 (cell12842 i)
      scalarRow12842.M scalarRow12842.H scalarRow12842.xi := by
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
    energy_allowance := scalarRow12842.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12842]
    centre_nonneg := (scalarRow12842.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12842])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12842
/-! Actual 12843 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12843 ≤ (1.035607556056 : ℝ) := by
  have hr : (113.326960605144 : ℝ) ≤ √(12843 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.326960605144 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12843 12843 (11 / 1000) ≤
    (0.008434771242 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12843) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.326960605144 : ℝ) ≤ √(12843 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12843)
  have hdiv : K / √(12843 : ℝ) ≤ K / 113.326960605144 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.326960605144 ≤ (0.008434771242 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12843.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12843 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12843 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12843 := gPlus_lower 12843
end BstLean.Part269.N12843

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12843
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035607556055 : ℝ) ≤ wn 12843 := by
  have hn : √(12843 : ℝ) ≤ 113.326960605145 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12843 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.326960605145 ≤ 2 / √(12843 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249027816 : ℝ) ≤ rhoBar 12843 BstLean.Part154.csC ∧
    rhoBar 12843 BstLean.Part154.csC ≤ 0.000249028201 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035607556055 : ℝ) / (1.295212 * 12843) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035607556056 : ℝ) / (1.29521 * 12843) := by gcongr
      _ ≤ (0.000249028201 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12843 BstLean.Part154.csC) ≤ 0.000996174820 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12843 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) ≤ 0.000190209320 ∧
    cc1 (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) ≤ 0.000121031474 ∧
    cc2 (rhoBar 12843 BstLean.Part154.csC) ≤ 0.000070259723 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12843 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12843 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12843 BstLean.Part154.csC * nuR (rhoBar 12843 BstLean.Part154.csC)) ≤ 0.000498071906 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249028201 : ℝ) * 0.000996174820 := by gcongr
      _ ≤ (0.000498071906 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12843 BstLean.Part154.csC) * nuR (rhoBar 12843 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996174820 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12843 BstLean.Part154.csC) * rhoBar 12843 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249028201 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249028201 / 2 + 0.399 * 0.000996174820 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190209320 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498071906 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121031474 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249028201 / 1.414213562 := by gcongr
      _ ≤ (0.000070259723 : ℝ) := by norm_num

end BstLean.Part269.N12843

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12843
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) ≤ 1.56243E-7 := by
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12843 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12843 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12843 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190209320 : ℝ) ^ 2 + 0.000121031474 ^ 2 + 3 * 0.000070259723 ^ 2 +
        2 * 0.797885 * 0.000190209320 * 0.000121031474 + 2 * 0.000190209320 * 0.000070259723 +
        4 * 0.797885 * 0.000121031474 * 0.000070259723 := by gcongr
    _ ≤ (1.56243E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12843 BstLean.Part154.csC Θ ≤ 0.002599009765 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12843 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12843 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12843 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035607556056 * 1.56243E-7 / (0.000249027816 : ℝ) := by gcongr
    _ ≤ 0.002599009765 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12843 BstLean.Part154.csC Θ ≤ 0.002883168286 + 0.000656725601 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12843 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12843 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035607556056 : ℝ) * ((2 * Θ * 0.000249028201 +
        (6863 / 10000) * 0.000249028201 * 12843 * 0.000996174820) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002883168286 + 0.000656725601 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12843 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12843 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12843 0.011 Θ ∧ gammaRatio 12843 0.011 Θ ≤ 0.000085609456 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12843 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035607556056 : ℝ) * 0.525 / ((1 - 0.011) * 12843) := by gcongr
      _ ≤ (0.000085609456 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12843 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12843 0.011 Θ) :=
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
    badAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12843 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12843 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12843 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12843 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12843 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12843 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12843 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12843 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12843 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12843 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035607556056 : ℝ) * 12843 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003392830502 + 0.003255735366 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12843

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12843
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12843 BstLean.Part154.csC) (piBar (rhoBar 12843 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12843 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12843 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12843 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12843 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12843 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12843 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12843 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12843 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12843 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12843 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052188142869 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12843) ≤ 0.010537982972 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12843 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035607556056)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010537982972 + 2 * 0.737676 / 12843) := by gcongr
    _ ≤ (0.052188142869 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12843 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12843

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12843
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509963170 : ℝ) ≤ plow 12843 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12843) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608691570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364480127) : eMP 12843 0.011 xi bn ≤ 0.001174881050 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12843 : ℝ) * (1 - 0.011))) ≤ 0.000580934516 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364480127 / (12843 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580934516 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580934516 : ℝ) + 3.141593 * 0.052608691570 / (12843 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174881050 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608691570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364480127) : PiBarMP 12843 12 0.011 xi bn ≤ 0.160341864745 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12843 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036938870138 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.701938758834 : ℝ) ≤ √((12843 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.326960605144 : ℝ) ≤ √(12843 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12843) ≤ 0.122939926990 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036938870138 + 0.052608691570 * 1.772454 / (2 * (112.701938758834 : ℝ))) * (1 + 0.001174881050) +
        8 / (12843 * 113.326960605144) + 0.122939926990 := by gcongr
    _ ≤ (0.160341864745 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608691570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364480127) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281553989433) :
    parallelOracle 12843 0.011 xi bn cd ≤ 0.161321208231 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12843 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12843 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509963170 : ℝ) ≤ plow 12843 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.326960605144 : ℝ) ≤ √(12843 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281553989433 : ℝ) / (2 * 0.560509963170 * 113.326960605144)) * 0.160341864745 +
        0.281553989433 ^ 2 / (2 * 0.560509963170 * 113.326960605144) := by gcongr
    _ ≤ (0.161321208231 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608691570) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364480127)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281553989433) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12843 12843 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509963170 : ℝ) ≤ plow 12843 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.326960605144 : ℝ) ≤ √(12843 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12843 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12843 Θ 1.22 ≤ 0.011701544743 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.326960605144 := by gcongr <;> linarith
      _ ≤ (0.011701544743 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12843 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12843 12843 0.011 ≤ 0.008434771242 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12843 12843 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12843 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12843 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12843 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12843 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161321208231 + 0.011701544743 + (0.008434771242 : ℝ) *
        (1 + 2 * (0.281553989433 + 0.011701544743) / (0.560509963170 * 113.326960605144))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12843]

end BstLean.Part269.N12843

/-! The original eight local profiles supply actual 12843 moment certificates. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12843 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052608691570 ∧
    0 ≤ bN 12843 BstLean.Part154.csC (groupTheta g) ∧ bN 12843 BstLean.Part154.csC (groupTheta g) ≤ 0.001364480127 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12843 12843 0.011
      (momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12843 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12843 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12843 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229365846564 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12843 0.011
      (momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12843 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12843
/-! The actual computed-centre upper energy formula at 12843. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12843

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12843)
open BstLean.Part268 (cell12843)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085083797540
  | 2 => 0.086019313141
  | 3 => 0.086951951318
  | 4 => 0.087882893242
  | 5 => 0.088813574983
  | 6 => 0.089745726308
  | 7 => 0.090681413306
  | 8 => 0.091623084913
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12843 12843 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12843 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12843

/-! Actual upper energy certificates on all 43 source endpoints at 12843. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12843)
open BstLean.Part268 (cell12843)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12843 (gMinus 12843) (1 - (cell12843 i).lower) ≤ 1 ∧
    energyUpper 12843 (gMinus 12843) (BstLean.Part211.gPlus 12843)
      (finiteEnergy 12843 12843 0.011) (1 - (cell12843 i).lower) ≤
      (cell12843 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨10,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨11,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨12,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨13,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨14,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨15,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨16,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨17,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨18,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨19,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨20,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨21,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨22,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨23,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨24,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨25,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨26,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨27,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨28,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨29,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨30,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨31,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨32,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨33,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨34,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨35,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨36,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨37,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨38,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨39,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨40,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨41,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨42,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨43,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨44,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨45,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨46,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨47,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨48,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨49,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨50,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨51,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12843) (by norm_num)
        (q := 1 - (cell12843 ⟨52,by decide⟩).lower)
        (by norm_num [cell12843]) (by norm_num [cell12843])
      exact ⟨E.1,E.2.trans (by norm_num [cell12843])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12843

/-! Source-cell containment and simple scalar guards at 12843. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12843)
open BstLean.Part268 (cell12843)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12843 ⟨10,by decide⟩).lower ∧ (cell12843 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12843 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12843 ⟨11,by decide⟩).lower ∧ (cell12843 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12843 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12843 ⟨12,by decide⟩).lower ∧ (cell12843 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12843 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12843 ⟨13,by decide⟩).lower ∧ (cell12843 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12843 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12843 ⟨14,by decide⟩).lower ∧ (cell12843 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12843 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12843 ⟨15,by decide⟩).lower ∧ (cell12843 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12843 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12843 ⟨16,by decide⟩).lower ∧ (cell12843 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12843 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12843 ⟨17,by decide⟩).lower ∧ (cell12843 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12843 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12843 ⟨18,by decide⟩).lower ∧ (cell12843 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12843 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12843 ⟨19,by decide⟩).lower ∧ (cell12843 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12843 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12843 ⟨20,by decide⟩).lower ∧ (cell12843 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12843 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12843 ⟨21,by decide⟩).lower ∧ (cell12843 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12843 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12843 ⟨22,by decide⟩).lower ∧ (cell12843 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12843 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12843 ⟨23,by decide⟩).lower ∧ (cell12843 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12843 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12843 ⟨24,by decide⟩).lower ∧ (cell12843 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12843 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12843 ⟨25,by decide⟩).lower ∧ (cell12843 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12843 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12843 ⟨26,by decide⟩).lower ∧ (cell12843 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12843 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12843 ⟨27,by decide⟩).lower ∧ (cell12843 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12843 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12843 ⟨28,by decide⟩).lower ∧ (cell12843 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12843 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12843 ⟨29,by decide⟩).lower ∧ (cell12843 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12843 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12843 ⟨30,by decide⟩).lower ∧ (cell12843 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12843 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12843 ⟨31,by decide⟩).lower ∧ (cell12843 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12843 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12843 ⟨32,by decide⟩).lower ∧ (cell12843 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12843 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12843 ⟨33,by decide⟩).lower ∧ (cell12843 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12843 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12843 ⟨34,by decide⟩).lower ∧ (cell12843 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12843 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12843 ⟨35,by decide⟩).lower ∧ (cell12843 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12843 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12843 ⟨36,by decide⟩).lower ∧ (cell12843 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12843 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12843 ⟨37,by decide⟩).lower ∧ (cell12843 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12843 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12843 ⟨38,by decide⟩).lower ∧ (cell12843 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12843 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12843 ⟨39,by decide⟩).lower ∧ (cell12843 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12843 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12843 ⟨40,by decide⟩).lower ∧ (cell12843 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12843 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12843 ⟨41,by decide⟩).lower ∧ (cell12843 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12843 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12843 ⟨42,by decide⟩).lower ∧ (cell12843 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12843 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12843 ⟨43,by decide⟩).lower ∧ (cell12843 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12843 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12843 ⟨44,by decide⟩).lower ∧ (cell12843 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12843 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12843 ⟨45,by decide⟩).lower ∧ (cell12843 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12843 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12843 ⟨46,by decide⟩).lower ∧ (cell12843 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12843 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12843 ⟨47,by decide⟩).lower ∧ (cell12843 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12843 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12843 ⟨48,by decide⟩).lower ∧ (cell12843 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12843 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12843 ⟨49,by decide⟩).lower ∧ (cell12843 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12843 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12843 ⟨50,by decide⟩).lower ∧ (cell12843 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12843 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12843 ⟨51,by decide⟩).lower ∧ (cell12843 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12843 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12843 ⟨52,by decide⟩).lower ∧ (cell12843 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12843 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12843 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12843 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12843,cell12843,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12843 i).lower ∧
    (cell12843 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12843 i).upper ≤ (0.532 : ℝ) ∧
    (cell12843 i).centre ≤ (0.1 : ℝ) ∧ (cell12843 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12843 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12843 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12843

/-! The local source numeric instances at 12843 have no network premises. -/
namespace BstLean.Part269.N12843
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12843)
open BstLean.Part268 (cell12843)

noncomputable def sourceNumerics12843 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12843 (cell12843 i)
      scalarRow12843.M scalarRow12843.H scalarRow12843.xi := by
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
    energy_allowance := scalarRow12843.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12843]
    centre_nonneg := (scalarRow12843.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12843])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12843
/-! Actual 12844 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12844 ≤ (1.035606157750 : ℝ) := by
  have hr : (113.331372532057 : ℝ) ≤ √(12844 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.331372532057 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12844 12844 (11 / 1000) ≤
    (0.008434442878 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12844) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.331372532057 : ℝ) ≤ √(12844 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12844)
  have hdiv : K / √(12844 : ℝ) ≤ K / 113.331372532057 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.331372532057 ≤ (0.008434442878 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12844.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12844 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12844 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12844 := gPlus_lower 12844
end BstLean.Part269.N12844

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12844
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035606157749 : ℝ) ≤ wn 12844 := by
  have hn : √(12844 : ℝ) ≤ 113.331372532058 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12844 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.331372532058 ≤ 2 / √(12844 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249008091 : ℝ) ≤ rhoBar 12844 BstLean.Part154.csC ∧
    rhoBar 12844 BstLean.Part154.csC ≤ 0.000249008476 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035606157749 : ℝ) / (1.295212 * 12844) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035606157750 : ℝ) / (1.29521 * 12844) := by gcongr
      _ ≤ (0.000249008476 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12844 BstLean.Part154.csC) ≤ 0.000996095910 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12844 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) ≤ 0.000190194253 ∧
    cc1 (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) ≤ 0.000121021887 ∧
    cc2 (rhoBar 12844 BstLean.Part154.csC) ≤ 0.000070254158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12844 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12844 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12844 BstLean.Part154.csC * nuR (rhoBar 12844 BstLean.Part154.csC)) ≤ 0.000498032454 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249008476 : ℝ) * 0.000996095910 := by gcongr
      _ ≤ (0.000498032454 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12844 BstLean.Part154.csC) * nuR (rhoBar 12844 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996095910 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12844 BstLean.Part154.csC) * rhoBar 12844 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249008476 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249008476 / 2 + 0.399 * 0.000996095910 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190194253 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498032454 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121021887 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249008476 / 1.414213562 := by gcongr
      _ ≤ (0.000070254158 : ℝ) := by norm_num

end BstLean.Part269.N12844

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12844
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) ≤ 1.56218E-7 := by
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12844 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12844 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12844 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190194253 : ℝ) ^ 2 + 0.000121021887 ^ 2 + 3 * 0.000070254158 ^ 2 +
        2 * 0.797885 * 0.000190194253 * 0.000121021887 + 2 * 0.000190194253 * 0.000070254158 +
        4 * 0.797885 * 0.000121021887 * 0.000070254158 := by gcongr
    _ ≤ (1.56218E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12844 BstLean.Part154.csC Θ ≤ 0.002598796242 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12844 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12844 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12844 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035606157750 * 1.56218E-7 / (0.000249008091 : ℝ) := by gcongr
    _ ≤ 0.002598796242 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12844 BstLean.Part154.csC Θ ≤ 0.002882932115 + 0.000656672697 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12844 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12844 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035606157750 : ℝ) * ((2 * Θ * 0.000249008476 +
        (6863 / 10000) * 0.000249008476 * 12844 * 0.000996095910) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002882932115 + 0.000656672697 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12844 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12844 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12844 0.011 Θ ∧ gammaRatio 12844 0.011 Θ ≤ 0.000085602675 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12844 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035606157750 : ℝ) * 0.525 / ((1 - 0.011) * 12844) := by gcongr
      _ ≤ (0.000085602675 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12844 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12844 0.011 Θ) :=
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
    badAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12844 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12844 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12844 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12844 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12844 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12844 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12844 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12844 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12844 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12844 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035606157750 : ℝ) * 12844 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003392594331 + 0.003255468939 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12844

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12844
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12844 BstLean.Part154.csC) (piBar (rhoBar 12844 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12844 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12844 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12844 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12844 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12844 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12844 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12844 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12844 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12844 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12844 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052186089305 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12844) ≤ 0.010537572734 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12844 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035606157750)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010537572734 + 2 * 0.737676 / 12844) := by gcongr
    _ ≤ (0.052186089305 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12844 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12844

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12844
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510007388 : ℝ) ≤ plow 12844 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12844) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608315524)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364368028) : eMP 12844 0.011 xi bn ≤ 0.001174786988 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12844 : ℝ) * (1 - 0.011))) ≤ 0.000580888038 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364368028 / (12844 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580888038 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580888038 : ℝ) + 3.141593 * 0.052608315524 / (12844 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174786988 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608315524)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364368028) : PiBarMP 12844 12 0.011 xi bn ≤ 0.160335536351 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12844 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036937352748 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.706326353049 : ℝ) ≤ √((12844 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.331372532057 : ℝ) ≤ √(12844 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12844) ≤ 0.122935141008 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036937352748 + 0.052608315524 * 1.772454 / (2 * (112.706326353049 : ℝ))) * (1 + 0.001174786988) +
        8 / (12844 * 113.331372532057) + 0.122935141008 := by gcongr
    _ ≤ (0.160335536351 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608315524)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364368028) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281551116116) :
    parallelOracle 12844 0.011 xi bn cd ≤ 0.161314811248 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12844 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12844 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510007388 : ℝ) ≤ plow 12844 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.331372532057 : ℝ) ≤ √(12844 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281551116116 : ℝ) / (2 * 0.560510007388 * 113.331372532057)) * 0.160335536351 +
        0.281551116116 ^ 2 / (2 * 0.560510007388 * 113.331372532057) := by gcongr
    _ ≤ (0.161314811248 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052608315524) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364368028)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281551116116) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12844 12844 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510007388 : ℝ) ≤ plow 12844 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.331372532057 : ℝ) ≤ √(12844 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12844 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12844 Θ 1.22 ≤ 0.011701089208 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.331372532057 := by gcongr <;> linarith
      _ ≤ (0.011701089208 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12844 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12844 12844 0.011 ≤ 0.008434442878 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12844 12844 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12844 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12844 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12844 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12844 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161314811248 + 0.011701089208 + (0.008434442878 : ℝ) *
        (1 + 2 * (0.281551116116 + 0.011701089208) / (0.560510007388 * 113.331372532057))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12844]

end BstLean.Part269.N12844

/-! The original eight local profiles supply actual 12844 moment certificates. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12844 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052608315524 ∧
    0 ≤ bN 12844 BstLean.Part154.csC (groupTheta g) ∧ bN 12844 BstLean.Part154.csC (groupTheta g) ≤ 0.001364368028 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12844 12844 0.011
      (momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12844 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12844 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12844 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229365026811 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12844 0.011
      (momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12844 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12844
/-! The actual computed-centre upper energy formula at 12844. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12844

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12844)
open BstLean.Part268 (cell12844)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085081026152
  | 2 => 0.086016494001
  | 3 => 0.086949077981
  | 4 => 0.087879957743
  | 5 => 0.088810567563
  | 6 => 0.089742635105
  | 7 => 0.090678224010
  | 8 => 0.091619780377
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12844 12844 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12844 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12844

/-! Actual upper energy certificates on all 43 source endpoints at 12844. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12844)
open BstLean.Part268 (cell12844)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12844 (gMinus 12844) (1 - (cell12844 i).lower) ≤ 1 ∧
    energyUpper 12844 (gMinus 12844) (BstLean.Part211.gPlus 12844)
      (finiteEnergy 12844 12844 0.011) (1 - (cell12844 i).lower) ≤
      (cell12844 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨10,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨11,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨12,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨13,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨14,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨15,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨16,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨17,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨18,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨19,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨20,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨21,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨22,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨23,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨24,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨25,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨26,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨27,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨28,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨29,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨30,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨31,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨32,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨33,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨34,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨35,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨36,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨37,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨38,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨39,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨40,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨41,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨42,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨43,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨44,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨45,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨46,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨47,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨48,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨49,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨50,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨51,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12844) (by norm_num)
        (q := 1 - (cell12844 ⟨52,by decide⟩).lower)
        (by norm_num [cell12844]) (by norm_num [cell12844])
      exact ⟨E.1,E.2.trans (by norm_num [cell12844])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12844

/-! Source-cell containment and simple scalar guards at 12844. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12844)
open BstLean.Part268 (cell12844)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12844 ⟨10,by decide⟩).lower ∧ (cell12844 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12844 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12844 ⟨11,by decide⟩).lower ∧ (cell12844 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12844 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12844 ⟨12,by decide⟩).lower ∧ (cell12844 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12844 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12844 ⟨13,by decide⟩).lower ∧ (cell12844 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12844 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12844 ⟨14,by decide⟩).lower ∧ (cell12844 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12844 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12844 ⟨15,by decide⟩).lower ∧ (cell12844 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12844 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12844 ⟨16,by decide⟩).lower ∧ (cell12844 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12844 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12844 ⟨17,by decide⟩).lower ∧ (cell12844 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12844 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12844 ⟨18,by decide⟩).lower ∧ (cell12844 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12844 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12844 ⟨19,by decide⟩).lower ∧ (cell12844 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12844 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12844 ⟨20,by decide⟩).lower ∧ (cell12844 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12844 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12844 ⟨21,by decide⟩).lower ∧ (cell12844 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12844 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12844 ⟨22,by decide⟩).lower ∧ (cell12844 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12844 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12844 ⟨23,by decide⟩).lower ∧ (cell12844 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12844 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12844 ⟨24,by decide⟩).lower ∧ (cell12844 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12844 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12844 ⟨25,by decide⟩).lower ∧ (cell12844 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12844 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12844 ⟨26,by decide⟩).lower ∧ (cell12844 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12844 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12844 ⟨27,by decide⟩).lower ∧ (cell12844 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12844 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12844 ⟨28,by decide⟩).lower ∧ (cell12844 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12844 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12844 ⟨29,by decide⟩).lower ∧ (cell12844 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12844 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12844 ⟨30,by decide⟩).lower ∧ (cell12844 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12844 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12844 ⟨31,by decide⟩).lower ∧ (cell12844 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12844 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12844 ⟨32,by decide⟩).lower ∧ (cell12844 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12844 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12844 ⟨33,by decide⟩).lower ∧ (cell12844 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12844 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12844 ⟨34,by decide⟩).lower ∧ (cell12844 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12844 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12844 ⟨35,by decide⟩).lower ∧ (cell12844 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12844 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12844 ⟨36,by decide⟩).lower ∧ (cell12844 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12844 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12844 ⟨37,by decide⟩).lower ∧ (cell12844 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12844 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12844 ⟨38,by decide⟩).lower ∧ (cell12844 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12844 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12844 ⟨39,by decide⟩).lower ∧ (cell12844 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12844 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12844 ⟨40,by decide⟩).lower ∧ (cell12844 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12844 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12844 ⟨41,by decide⟩).lower ∧ (cell12844 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12844 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12844 ⟨42,by decide⟩).lower ∧ (cell12844 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12844 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12844 ⟨43,by decide⟩).lower ∧ (cell12844 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12844 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12844 ⟨44,by decide⟩).lower ∧ (cell12844 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12844 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12844 ⟨45,by decide⟩).lower ∧ (cell12844 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12844 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12844 ⟨46,by decide⟩).lower ∧ (cell12844 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12844 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12844 ⟨47,by decide⟩).lower ∧ (cell12844 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12844 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12844 ⟨48,by decide⟩).lower ∧ (cell12844 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12844 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12844 ⟨49,by decide⟩).lower ∧ (cell12844 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12844 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12844 ⟨50,by decide⟩).lower ∧ (cell12844 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12844 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12844 ⟨51,by decide⟩).lower ∧ (cell12844 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12844 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12844 ⟨52,by decide⟩).lower ∧ (cell12844 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12844 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12844 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12844 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12844,cell12844,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12844 i).lower ∧
    (cell12844 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12844 i).upper ≤ (0.532 : ℝ) ∧
    (cell12844 i).centre ≤ (0.1 : ℝ) ∧ (cell12844 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12844 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12844 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12844

/-! The local source numeric instances at 12844 have no network premises. -/
namespace BstLean.Part269.N12844
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12844)
open BstLean.Part268 (cell12844)

noncomputable def sourceNumerics12844 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12844 (cell12844 i)
      scalarRow12844.M scalarRow12844.H scalarRow12844.xi := by
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
    energy_allowance := scalarRow12844.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12844]
    centre_nonneg := (scalarRow12844.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12844])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12844
/-! Actual 12845 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12845 ≤ (1.035604759607 : ℝ) := by
  have hr : (113.335784287223 : ℝ) ≤ √(12845 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.335784287223 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12845 12845 (11 / 1000) ≤
    (0.008434114553 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12845) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.335784287223 : ℝ) ≤ √(12845 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12845)
  have hdiv : K / √(12845 : ℝ) ≤ K / 113.335784287223 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.335784287223 ≤ (0.008434114553 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12845.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12845 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12845 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12845 := gPlus_lower 12845
end BstLean.Part269.N12845

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12845
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035604759606 : ℝ) ≤ wn 12845 := by
  have hn : √(12845 : ℝ) ≤ 113.335784287224 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12845 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.335784287224 ≤ 2 / √(12845 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248988369 : ℝ) ≤ rhoBar 12845 BstLean.Part154.csC ∧
    rhoBar 12845 BstLean.Part154.csC ≤ 0.000248988754 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035604759606 : ℝ) / (1.295212 * 12845) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035604759607 : ℝ) / (1.29521 * 12845) := by gcongr
      _ ≤ (0.000248988754 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12845 BstLean.Part154.csC) ≤ 0.000996017012 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12845 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) ≤ 0.000190179188 ∧
    cc1 (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) ≤ 0.000121012301 ∧
    cc2 (rhoBar 12845 BstLean.Part154.csC) ≤ 0.000070248593 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12845 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12845 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12845 BstLean.Part154.csC * nuR (rhoBar 12845 BstLean.Part154.csC)) ≤ 0.000497993007 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248988754 : ℝ) * 0.000996017012 := by gcongr
      _ ≤ (0.000497993007 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12845 BstLean.Part154.csC) * nuR (rhoBar 12845 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000996017012 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12845 BstLean.Part154.csC) * rhoBar 12845 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248988754 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248988754 / 2 + 0.399 * 0.000996017012 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190179188 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497993007 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121012301 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248988754 / 1.414213562 := by gcongr
      _ ≤ (0.000070248593 : ℝ) := by norm_num

end BstLean.Part269.N12845

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12845
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) ≤ 1.56193E-7 := by
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12845 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12845 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12845 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190179188 : ℝ) ^ 2 + 0.000121012301 ^ 2 + 3 * 0.000070248593 ^ 2 +
        2 * 0.797885 * 0.000190179188 * 0.000121012301 + 2 * 0.000190179188 * 0.000070248593 +
        4 * 0.797885 * 0.000121012301 * 0.000070248593 := by gcongr
    _ ≤ (1.56193E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12845 BstLean.Part154.csC Θ ≤ 0.002598582655 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12845 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12845 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12845 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035604759607 * 1.56193E-7 / (0.000248988369 : ℝ) := by gcongr
    _ ≤ 0.002598582655 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12845 BstLean.Part154.csC Θ ≤ 0.002882695980 + 0.000656619800 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12845 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12845 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035604759607 : ℝ) * ((2 * Θ * 0.000248988754 +
        (6863 / 10000) * 0.000248988754 * 12845 * 0.000996017012) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002882695980 + 0.000656619800 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12845 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12845 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12845 0.011 Θ ∧ gammaRatio 12845 0.011 Θ ≤ 0.000085595895 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12845 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035604759607 : ℝ) * 0.525 / ((1 - 0.011) * 12845) := by gcongr
      _ ≤ (0.000085595895 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12845 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12845 0.011 Θ) :=
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
    badAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12845 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12845 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12845 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12845 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12845 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12845 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12845 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12845 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12845 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12845 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035604759607 : ℝ) * 12845 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003392358196 + 0.003255202455 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12845

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12845
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12845 BstLean.Part154.csC) (piBar (rhoBar 12845 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12845 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12845 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12845 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12845 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12845 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12845 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12845 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12845 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12845 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12845 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052184035983 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12845) ≤ 0.010537162544 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12845 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035604759607)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010537162544 + 2 * 0.737676 / 12845) := by gcongr
    _ ≤ (0.052184035983 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12845 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12845

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12845
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510051599 : ℝ) ≤ plow 12845 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12845) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607939485)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364255894) : eMP 12845 0.011 xi bn ≤ 0.001174692918 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12845 : ℝ) * (1 - 0.011))) ≤ 0.000580841556 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364255894 / (12845 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580841556 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580841556 : ℝ) + 3.141593 * 0.052607939485 / (12845 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174692918 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607939485)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364255894) : PiBarMP 12845 12 0.011 xi bn ≤ 0.160329207982 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12845 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036935834823 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.710713776464 : ℝ) ≤ √((12845 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.335784287223 : ℝ) ≤ √(12845 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12845) ≤ 0.122930355584 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036935834823 + 0.052607939485 * 1.772454 / (2 * (112.710713776464 : ℝ))) * (1 + 0.001174692918) +
        8 / (12845 * 113.335784287223) + 0.122930355584 := by gcongr
    _ ≤ (0.160329207982 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607939485)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364255894) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281548243054) :
    parallelOracle 12845 0.011 xi bn cd ≤ 0.161308414300 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12845 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12845 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510051599 : ℝ) ≤ plow 12845 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.335784287223 : ℝ) ≤ √(12845 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281548243054 : ℝ) / (2 * 0.560510051599 * 113.335784287223)) * 0.160329207982 +
        0.281548243054 ^ 2 / (2 * 0.560510051599 * 113.335784287223) := by gcongr
    _ ≤ (0.161308414300 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607939485) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364255894)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281548243054) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12845 12845 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510051599 : ℝ) ≤ plow 12845 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.335784287223 : ℝ) ≤ √(12845 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12845 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12845 Θ 1.22 ≤ 0.011700633727 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.335784287223 := by gcongr <;> linarith
      _ ≤ (0.011700633727 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12845 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12845 12845 0.011 ≤ 0.008434114553 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12845 12845 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12845 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12845 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12845 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12845 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161308414300 + 0.011700633727 + (0.008434114553 : ℝ) *
        (1 + 2 * (0.281548243054 + 0.011700633727) / (0.560510051599 * 113.335784287223))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12845]

end BstLean.Part269.N12845

/-! The original eight local profiles supply actual 12845 moment certificates. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12845 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052607939485 ∧
    0 ≤ bN 12845 BstLean.Part154.csC (groupTheta g) ∧ bN 12845 BstLean.Part154.csC (groupTheta g) ≤ 0.001364255894 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12845 12845 0.011
      (momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12845 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12845 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12845 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229364207071 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12845 0.011
      (momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12845 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12845
/-! The actual computed-centre upper energy formula at 12845. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12845

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12845)
open BstLean.Part268 (cell12845)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085078255704
  | 2 => 0.086013675838
  | 3 => 0.086946205666
  | 4 => 0.087877023321
  | 5 => 0.088807561289
  | 6 => 0.089739545133
  | 7 => 0.090675036046
  | 8 => 0.091616477296
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12845 12845 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12845 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12845

/-! Actual upper energy certificates on all 43 source endpoints at 12845. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12845)
open BstLean.Part268 (cell12845)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12845 (gMinus 12845) (1 - (cell12845 i).lower) ≤ 1 ∧
    energyUpper 12845 (gMinus 12845) (BstLean.Part211.gPlus 12845)
      (finiteEnergy 12845 12845 0.011) (1 - (cell12845 i).lower) ≤
      (cell12845 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨10,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨11,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨12,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨13,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨14,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨15,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨16,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨17,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨18,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨19,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨20,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨21,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨22,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨23,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨24,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨25,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨26,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨27,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨28,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨29,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨30,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨31,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨32,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨33,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨34,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨35,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨36,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨37,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨38,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨39,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨40,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨41,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨42,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨43,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨44,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨45,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨46,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨47,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨48,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨49,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨50,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨51,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12845) (by norm_num)
        (q := 1 - (cell12845 ⟨52,by decide⟩).lower)
        (by norm_num [cell12845]) (by norm_num [cell12845])
      exact ⟨E.1,E.2.trans (by norm_num [cell12845])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12845

/-! Source-cell containment and simple scalar guards at 12845. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12845)
open BstLean.Part268 (cell12845)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12845 ⟨10,by decide⟩).lower ∧ (cell12845 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12845 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12845 ⟨11,by decide⟩).lower ∧ (cell12845 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12845 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12845 ⟨12,by decide⟩).lower ∧ (cell12845 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12845 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12845 ⟨13,by decide⟩).lower ∧ (cell12845 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12845 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12845 ⟨14,by decide⟩).lower ∧ (cell12845 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12845 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12845 ⟨15,by decide⟩).lower ∧ (cell12845 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12845 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12845 ⟨16,by decide⟩).lower ∧ (cell12845 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12845 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12845 ⟨17,by decide⟩).lower ∧ (cell12845 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12845 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12845 ⟨18,by decide⟩).lower ∧ (cell12845 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12845 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12845 ⟨19,by decide⟩).lower ∧ (cell12845 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12845 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12845 ⟨20,by decide⟩).lower ∧ (cell12845 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12845 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12845 ⟨21,by decide⟩).lower ∧ (cell12845 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12845 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12845 ⟨22,by decide⟩).lower ∧ (cell12845 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12845 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12845 ⟨23,by decide⟩).lower ∧ (cell12845 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12845 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12845 ⟨24,by decide⟩).lower ∧ (cell12845 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12845 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12845 ⟨25,by decide⟩).lower ∧ (cell12845 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12845 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12845 ⟨26,by decide⟩).lower ∧ (cell12845 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12845 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12845 ⟨27,by decide⟩).lower ∧ (cell12845 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12845 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12845 ⟨28,by decide⟩).lower ∧ (cell12845 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12845 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12845 ⟨29,by decide⟩).lower ∧ (cell12845 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12845 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12845 ⟨30,by decide⟩).lower ∧ (cell12845 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12845 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12845 ⟨31,by decide⟩).lower ∧ (cell12845 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12845 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12845 ⟨32,by decide⟩).lower ∧ (cell12845 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12845 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12845 ⟨33,by decide⟩).lower ∧ (cell12845 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12845 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12845 ⟨34,by decide⟩).lower ∧ (cell12845 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12845 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12845 ⟨35,by decide⟩).lower ∧ (cell12845 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12845 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12845 ⟨36,by decide⟩).lower ∧ (cell12845 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12845 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12845 ⟨37,by decide⟩).lower ∧ (cell12845 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12845 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12845 ⟨38,by decide⟩).lower ∧ (cell12845 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12845 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12845 ⟨39,by decide⟩).lower ∧ (cell12845 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12845 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12845 ⟨40,by decide⟩).lower ∧ (cell12845 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12845 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12845 ⟨41,by decide⟩).lower ∧ (cell12845 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12845 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12845 ⟨42,by decide⟩).lower ∧ (cell12845 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12845 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12845 ⟨43,by decide⟩).lower ∧ (cell12845 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12845 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12845 ⟨44,by decide⟩).lower ∧ (cell12845 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12845 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12845 ⟨45,by decide⟩).lower ∧ (cell12845 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12845 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12845 ⟨46,by decide⟩).lower ∧ (cell12845 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12845 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12845 ⟨47,by decide⟩).lower ∧ (cell12845 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12845 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12845 ⟨48,by decide⟩).lower ∧ (cell12845 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12845 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12845 ⟨49,by decide⟩).lower ∧ (cell12845 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12845 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12845 ⟨50,by decide⟩).lower ∧ (cell12845 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12845 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12845 ⟨51,by decide⟩).lower ∧ (cell12845 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12845 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12845 ⟨52,by decide⟩).lower ∧ (cell12845 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12845 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12845 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12845 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12845,cell12845,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12845 i).lower ∧
    (cell12845 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12845 i).upper ≤ (0.532 : ℝ) ∧
    (cell12845 i).centre ≤ (0.1 : ℝ) ∧ (cell12845 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12845 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12845 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12845

/-! The local source numeric instances at 12845 have no network premises. -/
namespace BstLean.Part269.N12845
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12845)
open BstLean.Part268 (cell12845)

noncomputable def sourceNumerics12845 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12845 (cell12845 i)
      scalarRow12845.M scalarRow12845.H scalarRow12845.xi := by
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
    energy_allowance := scalarRow12845.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12845]
    centre_nonneg := (scalarRow12845.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12845])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12845
/-! Actual 12846 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12846 ≤ (1.035603361629 : ℝ) := by
  have hr : (113.340195870661 : ℝ) ≤ √(12846 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.340195870661 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12846 12846 (11 / 1000) ≤
    (0.008433786266 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12846) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.340195870661 : ℝ) ≤ √(12846 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12846)
  have hdiv : K / √(12846 : ℝ) ≤ K / 113.340195870661 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.340195870661 ≤ (0.008433786266 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12846.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12846 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12846 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12846 := gPlus_lower 12846
end BstLean.Part269.N12846

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12846
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035603361628 : ℝ) ≤ wn 12846 := by
  have hn : √(12846 : ℝ) ≤ 113.340195870662 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12846 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.340195870662 ≤ 2 / √(12846 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248968650 : ℝ) ≤ rhoBar 12846 BstLean.Part154.csC ∧
    rhoBar 12846 BstLean.Part154.csC ≤ 0.000248969036 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035603361628 : ℝ) / (1.295212 * 12846) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035603361629 : ℝ) / (1.29521 * 12846) := by gcongr
      _ ≤ (0.000248969036 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12846 BstLean.Part154.csC) ≤ 0.000995938130 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12846 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) ≤ 0.000190164127 ∧
    cc1 (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) ≤ 0.000121002718 ∧
    cc2 (rhoBar 12846 BstLean.Part154.csC) ≤ 0.000070243030 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12846 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12846 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12846 BstLean.Part154.csC * nuR (rhoBar 12846 BstLean.Part154.csC)) ≤ 0.000497953569 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248969036 : ℝ) * 0.000995938130 := by gcongr
      _ ≤ (0.000497953569 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12846 BstLean.Part154.csC) * nuR (rhoBar 12846 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995938130 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12846 BstLean.Part154.csC) * rhoBar 12846 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248969036 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248969036 / 2 + 0.399 * 0.000995938130 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190164127 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497953569 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121002718 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248969036 / 1.414213562 := by gcongr
      _ ≤ (0.000070243030 : ℝ) := by norm_num

end BstLean.Part269.N12846

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12846
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) ≤ 1.56168E-7 := by
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12846 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12846 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12846 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190164127 : ℝ) ^ 2 + 0.000121002718 ^ 2 + 3 * 0.000070243030 ^ 2 +
        2 * 0.797885 * 0.000190164127 * 0.000121002718 + 2 * 0.000190164127 * 0.000070243030 +
        4 * 0.797885 * 0.000121002718 * 0.000070243030 := by gcongr
    _ ≤ (1.56168E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12846 BstLean.Part154.csC Θ ≤ 0.002598369004 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12846 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12846 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12846 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035603361629 * 1.56168E-7 / (0.000248968650 : ℝ) := by gcongr
    _ ≤ 0.002598369004 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12846 BstLean.Part154.csC Θ ≤ 0.002882459904 + 0.000656566915 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12846 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12846 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035603361629 : ℝ) * ((2 * Θ * 0.000248969036 +
        (6863 / 10000) * 0.000248969036 * 12846 * 0.000995938130) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002882459904 + 0.000656566915 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12846 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12846 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12846 0.011 Θ ∧ gammaRatio 12846 0.011 Θ ≤ 0.000085589117 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12846 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035603361629 : ℝ) * 0.525 / ((1 - 0.011) * 12846) := by gcongr
      _ ≤ (0.000085589117 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12846 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12846 0.011 Θ) :=
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
    badAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12846 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12846 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12846 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12846 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12846 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12846 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12846 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12846 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12846 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12846 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035603361629 : ℝ) * 12846 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003392122120 + 0.003254935919 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12846

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12846
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12846 BstLean.Part154.csC) (piBar (rhoBar 12846 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12846 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12846 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12846 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12846 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12846 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12846 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12846 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12846 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12846 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12846 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052181982903 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12846) ≤ 0.010536752402 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12846 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035603361629)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010536752402 + 2 * 0.737676 / 12846) := by gcongr
    _ ≤ (0.052181982903 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12846 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12846

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12846
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510095804 : ℝ) ≤ plow 12846 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12846) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607563478)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364143728) : eMP 12846 0.011 xi bn ≤ 0.001174598841 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12846 : ℝ) * (1 - 0.011))) ≤ 0.000580795070 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364143728 / (12846 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580795070 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580795070 : ℝ) + 3.141593 * 0.052607563478 / (12846 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174598841 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607563478)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364143728) : PiBarMP 12846 12 0.011 xi bn ≤ 0.160322879676 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12846 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036934316401 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.715101029099 : ℝ) ≤ √((12846 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.340195870661 : ℝ) ≤ √(12846 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12846) ≤ 0.122925570719 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036934316401 + 0.052607563478 * 1.772454 / (2 * (112.715101029099 : ℝ))) * (1 + 0.001174598841) +
        8 / (12846 * 113.340195870661) + 0.122925570719 := by gcongr
    _ ≤ (0.160322879676 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607563478)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364143728) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281545370300) :
    parallelOracle 12846 0.011 xi bn cd ≤ 0.161302017423 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12846 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12846 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510095804 : ℝ) ≤ plow 12846 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.340195870661 : ℝ) ≤ √(12846 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281545370300 : ℝ) / (2 * 0.560510095804 * 113.340195870661)) * 0.160322879676 +
        0.281545370300 ^ 2 / (2 * 0.560510095804 * 113.340195870661) := by gcongr
    _ ≤ (0.161302017423 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607563478) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364143728)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281545370300) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12846 12846 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510095804 : ℝ) ≤ plow 12846 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.340195870661 : ℝ) ≤ √(12846 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12846 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12846 Θ 1.22 ≤ 0.011700178298 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.340195870661 := by gcongr <;> linarith
      _ ≤ (0.011700178298 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12846 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12846 12846 0.011 ≤ 0.008433786266 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12846 12846 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12846 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12846 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12846 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12846 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161302017423 + 0.011700178298 + (0.008433786266 : ℝ) *
        (1 + 2 * (0.281545370300 + 0.011700178298) / (0.560510095804 * 113.340195870661))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12846]

end BstLean.Part269.N12846

/-! The original eight local profiles supply actual 12846 moment certificates. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12846 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052607563478 ∧
    0 ≤ bN 12846 BstLean.Part154.csC (groupTheta g) ∧ bN 12846 BstLean.Part154.csC (groupTheta g) ≤ 0.001364143728 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12846 12846 0.011
      (momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12846 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12846 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12846 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229363387397 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12846 0.011
      (momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12846 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12846
/-! The actual computed-centre upper energy formula at 12846. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12846

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12846)
open BstLean.Part268 (cell12846)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085075486195
  | 2 => 0.086010858651
  | 3 => 0.086943334372
  | 4 => 0.087874089977
  | 5 => 0.088804556161
  | 6 => 0.089736456390
  | 7 => 0.090671849412
  | 8 => 0.091613175667
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12846 12846 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12846 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12846

/-! Actual upper energy certificates on all 43 source endpoints at 12846. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12846)
open BstLean.Part268 (cell12846)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12846 (gMinus 12846) (1 - (cell12846 i).lower) ≤ 1 ∧
    energyUpper 12846 (gMinus 12846) (BstLean.Part211.gPlus 12846)
      (finiteEnergy 12846 12846 0.011) (1 - (cell12846 i).lower) ≤
      (cell12846 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨10,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨11,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨12,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨13,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨14,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨15,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨16,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨17,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨18,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨19,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨20,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨21,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨22,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨23,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨24,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨25,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨26,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨27,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨28,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨29,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨30,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨31,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨32,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨33,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨34,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨35,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨36,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨37,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨38,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨39,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨40,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨41,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨42,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨43,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨44,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨45,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨46,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨47,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨48,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨49,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨50,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨51,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12846) (by norm_num)
        (q := 1 - (cell12846 ⟨52,by decide⟩).lower)
        (by norm_num [cell12846]) (by norm_num [cell12846])
      exact ⟨E.1,E.2.trans (by norm_num [cell12846])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12846

/-! Source-cell containment and simple scalar guards at 12846. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12846)
open BstLean.Part268 (cell12846)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12846 ⟨10,by decide⟩).lower ∧ (cell12846 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12846 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12846 ⟨11,by decide⟩).lower ∧ (cell12846 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12846 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12846 ⟨12,by decide⟩).lower ∧ (cell12846 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12846 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12846 ⟨13,by decide⟩).lower ∧ (cell12846 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12846 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12846 ⟨14,by decide⟩).lower ∧ (cell12846 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12846 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12846 ⟨15,by decide⟩).lower ∧ (cell12846 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12846 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12846 ⟨16,by decide⟩).lower ∧ (cell12846 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12846 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12846 ⟨17,by decide⟩).lower ∧ (cell12846 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12846 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12846 ⟨18,by decide⟩).lower ∧ (cell12846 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12846 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12846 ⟨19,by decide⟩).lower ∧ (cell12846 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12846 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12846 ⟨20,by decide⟩).lower ∧ (cell12846 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12846 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12846 ⟨21,by decide⟩).lower ∧ (cell12846 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12846 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12846 ⟨22,by decide⟩).lower ∧ (cell12846 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12846 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12846 ⟨23,by decide⟩).lower ∧ (cell12846 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12846 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12846 ⟨24,by decide⟩).lower ∧ (cell12846 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12846 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12846 ⟨25,by decide⟩).lower ∧ (cell12846 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12846 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12846 ⟨26,by decide⟩).lower ∧ (cell12846 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12846 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12846 ⟨27,by decide⟩).lower ∧ (cell12846 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12846 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12846 ⟨28,by decide⟩).lower ∧ (cell12846 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12846 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12846 ⟨29,by decide⟩).lower ∧ (cell12846 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12846 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12846 ⟨30,by decide⟩).lower ∧ (cell12846 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12846 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12846 ⟨31,by decide⟩).lower ∧ (cell12846 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12846 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12846 ⟨32,by decide⟩).lower ∧ (cell12846 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12846 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12846 ⟨33,by decide⟩).lower ∧ (cell12846 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12846 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12846 ⟨34,by decide⟩).lower ∧ (cell12846 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12846 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12846 ⟨35,by decide⟩).lower ∧ (cell12846 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12846 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12846 ⟨36,by decide⟩).lower ∧ (cell12846 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12846 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12846 ⟨37,by decide⟩).lower ∧ (cell12846 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12846 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12846 ⟨38,by decide⟩).lower ∧ (cell12846 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12846 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12846 ⟨39,by decide⟩).lower ∧ (cell12846 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12846 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12846 ⟨40,by decide⟩).lower ∧ (cell12846 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12846 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12846 ⟨41,by decide⟩).lower ∧ (cell12846 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12846 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12846 ⟨42,by decide⟩).lower ∧ (cell12846 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12846 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12846 ⟨43,by decide⟩).lower ∧ (cell12846 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12846 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12846 ⟨44,by decide⟩).lower ∧ (cell12846 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12846 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12846 ⟨45,by decide⟩).lower ∧ (cell12846 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12846 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12846 ⟨46,by decide⟩).lower ∧ (cell12846 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12846 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12846 ⟨47,by decide⟩).lower ∧ (cell12846 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12846 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12846 ⟨48,by decide⟩).lower ∧ (cell12846 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12846 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12846 ⟨49,by decide⟩).lower ∧ (cell12846 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12846 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12846 ⟨50,by decide⟩).lower ∧ (cell12846 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12846 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12846 ⟨51,by decide⟩).lower ∧ (cell12846 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12846 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12846 ⟨52,by decide⟩).lower ∧ (cell12846 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12846 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12846 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12846 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12846,cell12846,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12846 i).lower ∧
    (cell12846 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12846 i).upper ≤ (0.532 : ℝ) ∧
    (cell12846 i).centre ≤ (0.1 : ℝ) ∧ (cell12846 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12846 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12846 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12846

/-! The local source numeric instances at 12846 have no network premises. -/
namespace BstLean.Part269.N12846
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12846)
open BstLean.Part268 (cell12846)

noncomputable def sourceNumerics12846 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12846 (cell12846 i)
      scalarRow12846.M scalarRow12846.H scalarRow12846.xi := by
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
    energy_allowance := scalarRow12846.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12846]
    centre_nonneg := (scalarRow12846.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12846])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12846
/-! Actual 12847 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12847 ≤ (1.035601963815 : ℝ) := by
  have hr : (113.344607282393 : ℝ) ≤ √(12847 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.344607282393 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12847 12847 (11 / 1000) ≤
    (0.008433458018 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12847) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.344607282393 : ℝ) ≤ √(12847 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12847)
  have hdiv : K / √(12847 : ℝ) ≤ K / 113.344607282393 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.344607282393 ≤ (0.008433458018 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12847.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12847 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12847 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12847 := gPlus_lower 12847
end BstLean.Part269.N12847

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12847
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035601963814 : ℝ) ≤ wn 12847 := by
  have hn : √(12847 : ℝ) ≤ 113.344607282394 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12847 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.344607282394 ≤ 2 / √(12847 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248948935 : ℝ) ≤ rhoBar 12847 BstLean.Part154.csC ∧
    rhoBar 12847 BstLean.Part154.csC ≤ 0.000248949320 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035601963814 : ℝ) / (1.295212 * 12847) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035601963815 : ℝ) / (1.29521 * 12847) := by gcongr
      _ ≤ (0.000248949320 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12847 BstLean.Part154.csC) ≤ 0.000995859256 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12847 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) ≤ 0.000190149067 ∧
    cc1 (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) ≤ 0.000120993135 ∧
    cc2 (rhoBar 12847 BstLean.Part154.csC) ≤ 0.000070237468 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12847 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12847 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12847 BstLean.Part154.csC * nuR (rhoBar 12847 BstLean.Part154.csC)) ≤ 0.000497914134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248949320 : ℝ) * 0.000995859256 := by gcongr
      _ ≤ (0.000497914134 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12847 BstLean.Part154.csC) * nuR (rhoBar 12847 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995859256 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12847 BstLean.Part154.csC) * rhoBar 12847 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248949320 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248949320 / 2 + 0.399 * 0.000995859256 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190149067 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497914134 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120993135 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248949320 / 1.414213562 := by gcongr
      _ ≤ (0.000070237468 : ℝ) := by norm_num

end BstLean.Part269.N12847

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12847
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) ≤ 1.56144E-7 := by
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12847 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12847 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12847 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190149067 : ℝ) ^ 2 + 0.000120993135 ^ 2 + 3 * 0.000070237468 ^ 2 +
        2 * 0.797885 * 0.000190149067 * 0.000120993135 + 2 * 0.000190149067 * 0.000070237468 +
        4 * 0.797885 * 0.000120993135 * 0.000070237468 := by gcongr
    _ ≤ (1.56144E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12847 BstLean.Part154.csC Θ ≤ 0.002598171919 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12847 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12847 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12847 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035601963815 * 1.56144E-7 / (0.000248948935 : ℝ) := by gcongr
    _ ≤ 0.002598171919 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12847 BstLean.Part154.csC Θ ≤ 0.002882223840 + 0.000656514035 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12847 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12847 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035601963815 : ℝ) * ((2 * Θ * 0.000248949320 +
        (6863 / 10000) * 0.000248949320 * 12847 * 0.000995859256) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002882223840 + 0.000656514035 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12847 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12847 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12847 0.011 Θ ∧ gammaRatio 12847 0.011 Θ ≤ 0.000085582339 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12847 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035601963815 : ℝ) * 0.525 / ((1 - 0.011) * 12847) := by gcongr
      _ ≤ (0.000085582339 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12847 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12847 0.011 Θ) :=
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
    badAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12847 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12847 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12847 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12847 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12847 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12847 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12847 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12847 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12847 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12847 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035601963815 : ℝ) * 12847 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003391886056 + 0.003254685954 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12847

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12847
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12847 BstLean.Part154.csC) (piBar (rhoBar 12847 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12847 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12847 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12847 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12847 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12847 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12847 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12847 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12847 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12847 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12847 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052179930065 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12847) ≤ 0.010536342308 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12847 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035601963815)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010536342308 + 2 * 0.737676 / 12847) := by gcongr
    _ ≤ (0.052179930065 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12847 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12847

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12847
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510140001 : ℝ) ≤ plow 12847 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12847) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607196182)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364040258) : eMP 12847 0.011 xi bn ≤ 0.001174508475 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12847 : ℝ) * (1 - 0.011))) ≤ 0.000580750439 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001364040258 / (12847 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580750439 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580750439 : ℝ) + 3.141593 * 0.052607196182 / (12847 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174508475 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607196182)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364040258) : PiBarMP 12847 12 0.011 xi bn ≤ 0.160316669944 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12847 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036932915645 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.719488110973 : ℝ) ≤ √((12847 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.344607282393 : ℝ) ≤ √(12847 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12847) ≤ 0.122920786413 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036932915645 + 0.052607196182 * 1.772454 / (2 * (112.719488110973 : ℝ))) * (1 + 0.001174508475) +
        8 / (12847 * 113.344607282393) + 0.122920786413 := by gcongr
    _ ≤ (0.160316669944 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607196182)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364040258) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281542516775) :
    parallelOracle 12847 0.011 xi bn cd ≤ 0.161295739499 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12847 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12847 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510140001 : ℝ) ≤ plow 12847 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.344607282393 : ℝ) ≤ √(12847 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281542516775 : ℝ) / (2 * 0.560510140001 * 113.344607282393)) * 0.160316669944 +
        0.281542516775 ^ 2 / (2 * 0.560510140001 * 113.344607282393) := by gcongr
    _ ≤ (0.161295739499 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052607196182) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001364040258)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281542516775) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12847 12847 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510140001 : ℝ) ≤ plow 12847 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.344607282393 : ℝ) ≤ √(12847 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12847 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12847 Θ 1.22 ≤ 0.011699722923 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.344607282393 := by gcongr <;> linarith
      _ ≤ (0.011699722923 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12847 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12847 12847 0.011 ≤ 0.008433458018 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12847 12847 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12847 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12847 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12847 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12847 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161295739499 + 0.011699722923 + (0.008433458018 : ℝ) *
        (1 + 2 * (0.281542516775 + 0.011699722923) / (0.560510140001 * 113.344607282393))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12847]

end BstLean.Part269.N12847

/-! The original eight local profiles supply actual 12847 moment certificates. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12847 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052607196182 ∧
    0 ≤ bN 12847 BstLean.Part154.csC (groupTheta g) ∧ bN 12847 BstLean.Part154.csC (groupTheta g) ≤ 0.001364040258 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12847 12847 0.011
      (momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12847 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12847 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12847 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229362586710 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12847 0.011
      (momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12847 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12847
/-! The actual computed-centre upper energy formula at 12847. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12847

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12847)
open BstLean.Part268 (cell12847)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085072717623
  | 2 => 0.086008042438
  | 3 => 0.086940464099
  | 4 => 0.087871157709
  | 5 => 0.088801552178
  | 6 => 0.089733368875
  | 7 => 0.090668664108
  | 8 => 0.091609875489
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12847 12847 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12847 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12847

/-! Actual upper energy certificates on all 43 source endpoints at 12847. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12847)
open BstLean.Part268 (cell12847)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12847 (gMinus 12847) (1 - (cell12847 i).lower) ≤ 1 ∧
    energyUpper 12847 (gMinus 12847) (BstLean.Part211.gPlus 12847)
      (finiteEnergy 12847 12847 0.011) (1 - (cell12847 i).lower) ≤
      (cell12847 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨10,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨11,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨12,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨13,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨14,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨15,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨16,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨17,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨18,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨19,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨20,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨21,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨22,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨23,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨24,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨25,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨26,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨27,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨28,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨29,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨30,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨31,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨32,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨33,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨34,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨35,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨36,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨37,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨38,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨39,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨40,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨41,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨42,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨43,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨44,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨45,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨46,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨47,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨48,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨49,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨50,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨51,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12847) (by norm_num)
        (q := 1 - (cell12847 ⟨52,by decide⟩).lower)
        (by norm_num [cell12847]) (by norm_num [cell12847])
      exact ⟨E.1,E.2.trans (by norm_num [cell12847])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12847

/-! Source-cell containment and simple scalar guards at 12847. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12847)
open BstLean.Part268 (cell12847)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12847 ⟨10,by decide⟩).lower ∧ (cell12847 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12847 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12847 ⟨11,by decide⟩).lower ∧ (cell12847 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12847 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12847 ⟨12,by decide⟩).lower ∧ (cell12847 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12847 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12847 ⟨13,by decide⟩).lower ∧ (cell12847 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12847 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12847 ⟨14,by decide⟩).lower ∧ (cell12847 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12847 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12847 ⟨15,by decide⟩).lower ∧ (cell12847 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12847 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12847 ⟨16,by decide⟩).lower ∧ (cell12847 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12847 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12847 ⟨17,by decide⟩).lower ∧ (cell12847 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12847 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12847 ⟨18,by decide⟩).lower ∧ (cell12847 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12847 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12847 ⟨19,by decide⟩).lower ∧ (cell12847 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12847 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12847 ⟨20,by decide⟩).lower ∧ (cell12847 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12847 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12847 ⟨21,by decide⟩).lower ∧ (cell12847 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12847 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12847 ⟨22,by decide⟩).lower ∧ (cell12847 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12847 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12847 ⟨23,by decide⟩).lower ∧ (cell12847 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12847 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12847 ⟨24,by decide⟩).lower ∧ (cell12847 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12847 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12847 ⟨25,by decide⟩).lower ∧ (cell12847 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12847 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12847 ⟨26,by decide⟩).lower ∧ (cell12847 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12847 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12847 ⟨27,by decide⟩).lower ∧ (cell12847 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12847 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12847 ⟨28,by decide⟩).lower ∧ (cell12847 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12847 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12847 ⟨29,by decide⟩).lower ∧ (cell12847 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12847 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12847 ⟨30,by decide⟩).lower ∧ (cell12847 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12847 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12847 ⟨31,by decide⟩).lower ∧ (cell12847 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12847 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12847 ⟨32,by decide⟩).lower ∧ (cell12847 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12847 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12847 ⟨33,by decide⟩).lower ∧ (cell12847 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12847 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12847 ⟨34,by decide⟩).lower ∧ (cell12847 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12847 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12847 ⟨35,by decide⟩).lower ∧ (cell12847 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12847 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12847 ⟨36,by decide⟩).lower ∧ (cell12847 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12847 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12847 ⟨37,by decide⟩).lower ∧ (cell12847 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12847 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12847 ⟨38,by decide⟩).lower ∧ (cell12847 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12847 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12847 ⟨39,by decide⟩).lower ∧ (cell12847 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12847 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12847 ⟨40,by decide⟩).lower ∧ (cell12847 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12847 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12847 ⟨41,by decide⟩).lower ∧ (cell12847 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12847 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12847 ⟨42,by decide⟩).lower ∧ (cell12847 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12847 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12847 ⟨43,by decide⟩).lower ∧ (cell12847 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12847 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12847 ⟨44,by decide⟩).lower ∧ (cell12847 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12847 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12847 ⟨45,by decide⟩).lower ∧ (cell12847 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12847 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12847 ⟨46,by decide⟩).lower ∧ (cell12847 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12847 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12847 ⟨47,by decide⟩).lower ∧ (cell12847 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12847 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12847 ⟨48,by decide⟩).lower ∧ (cell12847 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12847 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12847 ⟨49,by decide⟩).lower ∧ (cell12847 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12847 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12847 ⟨50,by decide⟩).lower ∧ (cell12847 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12847 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12847 ⟨51,by decide⟩).lower ∧ (cell12847 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12847 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12847 ⟨52,by decide⟩).lower ∧ (cell12847 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12847 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12847 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12847 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12847,cell12847,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12847 i).lower ∧
    (cell12847 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12847 i).upper ≤ (0.532 : ℝ) ∧
    (cell12847 i).centre ≤ (0.1 : ℝ) ∧ (cell12847 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12847 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12847 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12847

/-! The local source numeric instances at 12847 have no network premises. -/
namespace BstLean.Part269.N12847
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12847)
open BstLean.Part268 (cell12847)

noncomputable def sourceNumerics12847 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12847 (cell12847 i)
      scalarRow12847.M scalarRow12847.H scalarRow12847.xi := by
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
    energy_allowance := scalarRow12847.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12847]
    centre_nonneg := (scalarRow12847.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12847])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12847
/-! Actual 12848 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12848 ≤ (1.035600566166 : ℝ) := by
  have hr : (113.349018522438 : ℝ) ≤ √(12848 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.349018522438 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12848 12848 (11 / 1000) ≤
    (0.008433129808 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12848) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.349018522438 : ℝ) ≤ √(12848 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12848)
  have hdiv : K / √(12848 : ℝ) ≤ K / 113.349018522438 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.349018522438 ≤ (0.008433129808 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12848.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12848 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12848 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12848 := gPlus_lower 12848
end BstLean.Part269.N12848

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12848
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035600566165 : ℝ) ≤ wn 12848 := by
  have hn : √(12848 : ℝ) ≤ 113.349018522439 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12848 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.349018522439 ≤ 2 / √(12848 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248929222 : ℝ) ≤ rhoBar 12848 BstLean.Part154.csC ∧
    rhoBar 12848 BstLean.Part154.csC ≤ 0.000248929608 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035600566165 : ℝ) / (1.295212 * 12848) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035600566166 : ℝ) / (1.29521 * 12848) := by gcongr
      _ ≤ (0.000248929608 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12848 BstLean.Part154.csC) ≤ 0.000995780398 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12848 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) ≤ 0.000190134010 ∧
    cc1 (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) ≤ 0.000120983555 ∧
    cc2 (rhoBar 12848 BstLean.Part154.csC) ≤ 0.000070231906 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12848 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12848 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12848 BstLean.Part154.csC * nuR (rhoBar 12848 BstLean.Part154.csC)) ≤ 0.000497874708 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248929608 : ℝ) * 0.000995780398 := by gcongr
      _ ≤ (0.000497874708 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12848 BstLean.Part154.csC) * nuR (rhoBar 12848 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995780398 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12848 BstLean.Part154.csC) * rhoBar 12848 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248929608 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248929608 / 2 + 0.399 * 0.000995780398 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190134010 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497874708 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120983555 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248929608 / 1.414213562 := by gcongr
      _ ≤ (0.000070231906 : ℝ) := by norm_num

end BstLean.Part269.N12848

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12848
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) ≤ 1.56119E-7 := by
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12848 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12848 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12848 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190134010 : ℝ) ^ 2 + 0.000120983555 ^ 2 + 3 * 0.000070231906 ^ 2 +
        2 * 0.797885 * 0.000190134010 * 0.000120983555 + 2 * 0.000190134010 * 0.000070231906 +
        4 * 0.797885 * 0.000120983555 * 0.000070231906 := by gcongr
    _ ≤ (1.56119E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12848 BstLean.Part154.csC Θ ≤ 0.002597958143 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12848 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12848 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12848 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035600566166 * 1.56119E-7 / (0.000248929222 : ℝ) := by gcongr
    _ ≤ 0.002597958143 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12848 BstLean.Part154.csC Θ ≤ 0.002881987834 + 0.000656461165 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12848 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12848 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035600566166 : ℝ) * ((2 * Θ * 0.000248929608 +
        (6863 / 10000) * 0.000248929608 * 12848 * 0.000995780398) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002881987834 + 0.000656461165 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12848 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12848 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12848 0.011 Θ ∧ gammaRatio 12848 0.011 Θ ≤ 0.000085575562 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12848 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035600566166 : ℝ) * 0.525 / ((1 - 0.011) * 12848) := by gcongr
      _ ≤ (0.000085575562 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12848 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12848 0.011 Θ) :=
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
    badAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12848 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12848 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12848 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12848 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12848 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12848 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12848 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12848 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12848 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12848 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035600566166 : ℝ) * 12848 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003391650050 + 0.003254419308 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12848

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12848
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12848 BstLean.Part154.csC) (piBar (rhoBar 12848 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12848 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12848 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12848 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12848 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12848 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12848 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12848 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12848 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12848 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12848 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052177877469 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12848) ≤ 0.010535932262 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12848 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035600566166)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010535932262 + 2 * 0.737676 / 12848) := by gcongr
    _ ≤ (0.052177877469 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12848 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12848

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12848
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510184192 : ℝ) ≤ plow 12848 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12848) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606820187)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363928026) : eMP 12848 0.011 xi bn ≤ 0.001174414386 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12848 : ℝ) * (1 - 0.011))) ≤ 0.000580703947 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363928026 / (12848 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580703947 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580703947 : ℝ) + 3.141593 * 0.052606820187 / (12848 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174414386 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606820187)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363928026) : PiBarMP 12848 12 0.011 xi bn ≤ 0.160310341746 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12848 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036931396210 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.723875022108 : ℝ) ≤ √((12848 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.349018522438 : ℝ) ≤ √(12848 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12848) ≤ 0.122916002665 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036931396210 + 0.052606820187 * 1.772454 / (2 * (112.723875022108 : ℝ))) * (1 + 0.001174414386) +
        8 / (12848 * 113.349018522438) + 0.122916002665 := by gcongr
    _ ≤ (0.160310341746 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606820187)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363928026) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281539644525) :
    parallelOracle 12848 0.011 xi bn cd ≤ 0.161289342748 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12848 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12848 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510184192 : ℝ) ≤ plow 12848 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.349018522438 : ℝ) ≤ √(12848 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281539644525 : ℝ) / (2 * 0.560510184192 * 113.349018522438)) * 0.160310341746 +
        0.281539644525 ^ 2 / (2 * 0.560510184192 * 113.349018522438) := by gcongr
    _ ≤ (0.161289342748 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606820187) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363928026)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281539644525) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12848 12848 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510184192 : ℝ) ≤ plow 12848 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.349018522438 : ℝ) ≤ √(12848 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12848 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12848 Θ 1.22 ≤ 0.011699267601 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.349018522438 := by gcongr <;> linarith
      _ ≤ (0.011699267601 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12848 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12848 12848 0.011 ≤ 0.008433129808 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12848 12848 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12848 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12848 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12848 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12848 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161289342748 + 0.011699267601 + (0.008433129808 : ℝ) *
        (1 + 2 * (0.281539644525 + 0.011699267601) / (0.560510184192 * 113.349018522438))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12848]

end BstLean.Part269.N12848

/-! The original eight local profiles supply actual 12848 moment certificates. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12848 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052606820187 ∧
    0 ≤ bN 12848 BstLean.Part154.csC (groupTheta g) ∧ bN 12848 BstLean.Part154.csC (groupTheta g) ≤ 0.001363928026 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12848 12848 0.011
      (momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12848 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12848 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12848 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229361767056 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12848 0.011
      (momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12848 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12848
/-! The actual computed-centre upper energy formula at 12848. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12848

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12848)
open BstLean.Part268 (cell12848)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085069949989
  | 2 => 0.086005227199
  | 3 => 0.086937594844
  | 4 => 0.087868226516
  | 5 => 0.088798549338
  | 6 => 0.089730282587
  | 7 => 0.090665480132
  | 8 => 0.091606576761
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12848 12848 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12848 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12848

/-! Actual upper energy certificates on all 43 source endpoints at 12848. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12848)
open BstLean.Part268 (cell12848)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12848 (gMinus 12848) (1 - (cell12848 i).lower) ≤ 1 ∧
    energyUpper 12848 (gMinus 12848) (BstLean.Part211.gPlus 12848)
      (finiteEnergy 12848 12848 0.011) (1 - (cell12848 i).lower) ≤
      (cell12848 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨10,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨11,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨12,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨13,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨14,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨15,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨16,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨17,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨18,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨19,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨20,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨21,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨22,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨23,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨24,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨25,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨26,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨27,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨28,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨29,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨30,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨31,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨32,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨33,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨34,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨35,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨36,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨37,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨38,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨39,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨40,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨41,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨42,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨43,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨44,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨45,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨46,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨47,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨48,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨49,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨50,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨51,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12848) (by norm_num)
        (q := 1 - (cell12848 ⟨52,by decide⟩).lower)
        (by norm_num [cell12848]) (by norm_num [cell12848])
      exact ⟨E.1,E.2.trans (by norm_num [cell12848])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12848

/-! Source-cell containment and simple scalar guards at 12848. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12848)
open BstLean.Part268 (cell12848)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12848 ⟨10,by decide⟩).lower ∧ (cell12848 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12848 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12848 ⟨11,by decide⟩).lower ∧ (cell12848 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12848 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12848 ⟨12,by decide⟩).lower ∧ (cell12848 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12848 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12848 ⟨13,by decide⟩).lower ∧ (cell12848 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12848 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12848 ⟨14,by decide⟩).lower ∧ (cell12848 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12848 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12848 ⟨15,by decide⟩).lower ∧ (cell12848 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12848 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12848 ⟨16,by decide⟩).lower ∧ (cell12848 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12848 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12848 ⟨17,by decide⟩).lower ∧ (cell12848 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12848 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12848 ⟨18,by decide⟩).lower ∧ (cell12848 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12848 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12848 ⟨19,by decide⟩).lower ∧ (cell12848 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12848 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12848 ⟨20,by decide⟩).lower ∧ (cell12848 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12848 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12848 ⟨21,by decide⟩).lower ∧ (cell12848 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12848 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12848 ⟨22,by decide⟩).lower ∧ (cell12848 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12848 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12848 ⟨23,by decide⟩).lower ∧ (cell12848 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12848 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12848 ⟨24,by decide⟩).lower ∧ (cell12848 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12848 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12848 ⟨25,by decide⟩).lower ∧ (cell12848 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12848 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12848 ⟨26,by decide⟩).lower ∧ (cell12848 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12848 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12848 ⟨27,by decide⟩).lower ∧ (cell12848 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12848 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12848 ⟨28,by decide⟩).lower ∧ (cell12848 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12848 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12848 ⟨29,by decide⟩).lower ∧ (cell12848 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12848 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12848 ⟨30,by decide⟩).lower ∧ (cell12848 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12848 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12848 ⟨31,by decide⟩).lower ∧ (cell12848 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12848 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12848 ⟨32,by decide⟩).lower ∧ (cell12848 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12848 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12848 ⟨33,by decide⟩).lower ∧ (cell12848 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12848 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12848 ⟨34,by decide⟩).lower ∧ (cell12848 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12848 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12848 ⟨35,by decide⟩).lower ∧ (cell12848 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12848 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12848 ⟨36,by decide⟩).lower ∧ (cell12848 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12848 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12848 ⟨37,by decide⟩).lower ∧ (cell12848 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12848 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12848 ⟨38,by decide⟩).lower ∧ (cell12848 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12848 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12848 ⟨39,by decide⟩).lower ∧ (cell12848 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12848 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12848 ⟨40,by decide⟩).lower ∧ (cell12848 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12848 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12848 ⟨41,by decide⟩).lower ∧ (cell12848 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12848 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12848 ⟨42,by decide⟩).lower ∧ (cell12848 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12848 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12848 ⟨43,by decide⟩).lower ∧ (cell12848 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12848 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12848 ⟨44,by decide⟩).lower ∧ (cell12848 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12848 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12848 ⟨45,by decide⟩).lower ∧ (cell12848 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12848 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12848 ⟨46,by decide⟩).lower ∧ (cell12848 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12848 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12848 ⟨47,by decide⟩).lower ∧ (cell12848 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12848 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12848 ⟨48,by decide⟩).lower ∧ (cell12848 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12848 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12848 ⟨49,by decide⟩).lower ∧ (cell12848 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12848 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12848 ⟨50,by decide⟩).lower ∧ (cell12848 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12848 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12848 ⟨51,by decide⟩).lower ∧ (cell12848 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12848 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12848 ⟨52,by decide⟩).lower ∧ (cell12848 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12848 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12848 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12848 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12848,cell12848,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12848 i).lower ∧
    (cell12848 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12848 i).upper ≤ (0.532 : ℝ) ∧
    (cell12848 i).centre ≤ (0.1 : ℝ) ∧ (cell12848 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12848 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12848 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12848

/-! The local source numeric instances at 12848 have no network premises. -/
namespace BstLean.Part269.N12848
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12848)
open BstLean.Part268 (cell12848)

noncomputable def sourceNumerics12848 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12848 (cell12848 i)
      scalarRow12848.M scalarRow12848.H scalarRow12848.xi := by
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
    energy_allowance := scalarRow12848.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12848]
    centre_nonneg := (scalarRow12848.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12848])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12848
/-! Actual 12849 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12849 ≤ (1.035599168680 : ℝ) := by
  have hr : (113.353429590815 : ℝ) ≤ √(12849 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.353429590815 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12849 12849 (11 / 1000) ≤
    (0.008432801636 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12849) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.353429590815 : ℝ) ≤ √(12849 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12849)
  have hdiv : K / √(12849 : ℝ) ≤ K / 113.353429590815 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.353429590815 ≤ (0.008432801636 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12849.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12849 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12849 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12849 := gPlus_lower 12849
end BstLean.Part269.N12849

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12849
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035599168679 : ℝ) ≤ wn 12849 := by
  have hn : √(12849 : ℝ) ≤ 113.353429590816 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12849 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.353429590816 ≤ 2 / √(12849 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248909513 : ℝ) ≤ rhoBar 12849 BstLean.Part154.csC ∧
    rhoBar 12849 BstLean.Part154.csC ≤ 0.000248909898 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035599168679 : ℝ) / (1.295212 * 12849) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035599168680 : ℝ) / (1.29521 * 12849) := by gcongr
      _ ≤ (0.000248909898 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12849 BstLean.Part154.csC) ≤ 0.000995701549 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12849 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) ≤ 0.000190118955 ∧
    cc1 (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) ≤ 0.000120973975 ∧
    cc2 (rhoBar 12849 BstLean.Part154.csC) ≤ 0.000070226345 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12849 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12849 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12849 BstLean.Part154.csC * nuR (rhoBar 12849 BstLean.Part154.csC)) ≤ 0.000497835286 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248909898 : ℝ) * 0.000995701549 := by gcongr
      _ ≤ (0.000497835286 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12849 BstLean.Part154.csC) * nuR (rhoBar 12849 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995701549 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12849 BstLean.Part154.csC) * rhoBar 12849 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248909898 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248909898 / 2 + 0.399 * 0.000995701549 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190118955 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497835286 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120973975 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248909898 / 1.414213562 := by gcongr
      _ ≤ (0.000070226345 : ℝ) := by norm_num

end BstLean.Part269.N12849

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12849
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) ≤ 1.56094E-7 := by
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12849 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12849 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12849 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190118955 : ℝ) ^ 2 + 0.000120973975 ^ 2 + 3 * 0.000070226345 ^ 2 +
        2 * 0.797885 * 0.000190118955 * 0.000120973975 + 2 * 0.000190118955 * 0.000070226345 +
        4 * 0.797885 * 0.000120973975 * 0.000070226345 := by gcongr
    _ ≤ (1.56094E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12849 BstLean.Part154.csC Θ ≤ 0.002597744292 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12849 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12849 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12849 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035599168680 * 1.56094E-7 / (0.000248909513 : ℝ) := by gcongr
    _ ≤ 0.002597744292 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12849 BstLean.Part154.csC Θ ≤ 0.002881751844 + 0.000656408302 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12849 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12849 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035599168680 : ℝ) * ((2 * Θ * 0.000248909898 +
        (6863 / 10000) * 0.000248909898 * 12849 * 0.000995701549) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002881751844 + 0.000656408302 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12849 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12849 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12849 0.011 Θ ∧ gammaRatio 12849 0.011 Θ ≤ 0.000085568787 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12849 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035599168680 : ℝ) * 0.525 / ((1 - 0.011) * 12849) := by gcongr
      _ ≤ (0.000085568787 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12849 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12849 0.011 Θ) :=
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
    badAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000509662216 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12849 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12849 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12849 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12849 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12849 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12849 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12849 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12849 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12849 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12849 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035599168680 : ℝ) * 12849 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000509662216 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003391414060 + 0.003254152594 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12849

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12849
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12849 BstLean.Part154.csC) (piBar (rhoBar 12849 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12849 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12849 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12849 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12849 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12849 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12849 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12849 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12849 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12849 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12849 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052175825115 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12849) ≤ 0.010535522264 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12849 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035599168680)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010535522264 + 2 * 0.737676 / 12849) := by gcongr
    _ ≤ (0.052175825115 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12849 12 ≤ 0.0015 := by
  exact BstLean.Part269.S19.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12849

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12849
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510228375 : ℝ) ≤ plow 12849 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12849) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606444172)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363815754) : eMP 12849 0.011 xi bn ≤ 0.001174320285 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12849 : ℝ) * (1 - 0.011))) ≤ 0.000580657449 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363815754 / (12849 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580657449 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580657449 : ℝ) + 3.141593 * 0.052606444172 / (12849 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174320285 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606444172)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363815754) : PiBarMP 12849 12 0.011 xi bn ≤ 0.160304013505 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12849 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036929876171 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.728261762523 : ℝ) ≤ √((12849 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.353429590815 : ℝ) ≤ √(12849 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12849) ≤ 0.122911219476 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036929876171 + 0.052606444172 * 1.772454 / (2 * (112.728261762523 : ℝ))) * (1 + 0.001174320285) +
        8 / (12849 * 113.353429590815) + 0.122911219476 := by gcongr
    _ ≤ (0.160304013505 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606444172)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363815754) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281536772471) :
    parallelOracle 12849 0.011 xi bn cd ≤ 0.161282945962 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12849 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12849 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510228375 : ℝ) ≤ plow 12849 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.353429590815 : ℝ) ≤ √(12849 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281536772471 : ℝ) / (2 * 0.560510228375 * 113.353429590815)) * 0.160304013505 +
        0.281536772471 ^ 2 / (2 * 0.560510228375 * 113.353429590815) := by gcongr
    _ ≤ (0.161282945962 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052606444172) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363815754)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281536772471) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12849 12849 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510228375 : ℝ) ≤ plow 12849 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.353429590815 : ℝ) ≤ √(12849 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12849 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12849 Θ 1.22 ≤ 0.011698812333 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.353429590815 := by gcongr <;> linarith
      _ ≤ (0.011698812333 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12849 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12849 12849 0.011 ≤ 0.008432801636 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12849 12849 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12849 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12849 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12849 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12849 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161282945962 + 0.011698812333 + (0.008432801636 : ℝ) *
        (1 + 2 * (0.281536772471 + 0.011698812333) / (0.560510228375 * 113.353429590815))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12849]

end BstLean.Part269.N12849

/-! The original eight local profiles supply actual 12849 moment certificates. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12849 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052606444172 ∧
    0 ≤ bN 12849 BstLean.Part154.csC (groupTheta g) ∧ bN 12849 BstLean.Part154.csC (groupTheta g) ≤ 0.001363815754 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12849 12849 0.011
      (momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12849 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12849 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12849 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229360947356 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12849 0.011
      (momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12849 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12849
/-! The actual computed-centre upper energy formula at 12849. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12849

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12849)
open BstLean.Part268 (cell12849)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085067183290
  | 2 => 0.086002412933
  | 3 => 0.086934726608
  | 4 => 0.087865296397
  | 5 => 0.088795547641
  | 6 => 0.089727197524
  | 7 => 0.090662297482
  | 8 => 0.091603279481
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12849 12849 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12849 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12849

/-! Actual upper energy certificates on all 43 source endpoints at 12849. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12849)
open BstLean.Part268 (cell12849)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12849 (gMinus 12849) (1 - (cell12849 i).lower) ≤ 1 ∧
    energyUpper 12849 (gMinus 12849) (BstLean.Part211.gPlus 12849)
      (finiteEnergy 12849 12849 0.011) (1 - (cell12849 i).lower) ≤
      (cell12849 i).energy := by
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
      have E := BstLean.Part269.S19.uniformEnergy10 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨10,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy11 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨11,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy12 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨12,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy13 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨13,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy14 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨14,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy15 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨15,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy16 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨16,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy17 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨17,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy18 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨18,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy19 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨19,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy20 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨20,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy21 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨21,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy22 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨22,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy23 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨23,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy24 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨24,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy25 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨25,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy26 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨26,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy27 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨27,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy28 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨28,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy29 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨29,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy30 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨30,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy31 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨31,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy32 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨32,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy33 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨33,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy34 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨34,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy35 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨35,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy36 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨36,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy37 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨37,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy38 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨38,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy39 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨39,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy40 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨40,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy41 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨41,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy42 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨42,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy43 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨43,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy44 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨44,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy45 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨45,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy46 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨46,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy47 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨47,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy48 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨48,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy49 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨49,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy50 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨50,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy51 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨51,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S19.uniformEnergy52 (n := 12849) (by norm_num)
        (q := 1 - (cell12849 ⟨52,by decide⟩).lower)
        (by norm_num [cell12849]) (by norm_num [cell12849])
      exact ⟨E.1,E.2.trans (by norm_num [cell12849])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12849

/-! Source-cell containment and simple scalar guards at 12849. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12849)
open BstLean.Part268 (cell12849)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12849 ⟨10,by decide⟩).lower ∧ (cell12849 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12849 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12849 ⟨11,by decide⟩).lower ∧ (cell12849 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12849 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12849 ⟨12,by decide⟩).lower ∧ (cell12849 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12849 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12849 ⟨13,by decide⟩).lower ∧ (cell12849 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12849 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12849 ⟨14,by decide⟩).lower ∧ (cell12849 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12849 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12849 ⟨15,by decide⟩).lower ∧ (cell12849 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12849 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12849 ⟨16,by decide⟩).lower ∧ (cell12849 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12849 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12849 ⟨17,by decide⟩).lower ∧ (cell12849 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12849 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12849 ⟨18,by decide⟩).lower ∧ (cell12849 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12849 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12849 ⟨19,by decide⟩).lower ∧ (cell12849 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12849 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12849 ⟨20,by decide⟩).lower ∧ (cell12849 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12849 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12849 ⟨21,by decide⟩).lower ∧ (cell12849 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12849 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12849 ⟨22,by decide⟩).lower ∧ (cell12849 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12849 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12849 ⟨23,by decide⟩).lower ∧ (cell12849 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12849 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12849 ⟨24,by decide⟩).lower ∧ (cell12849 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12849 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12849 ⟨25,by decide⟩).lower ∧ (cell12849 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12849 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12849 ⟨26,by decide⟩).lower ∧ (cell12849 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12849 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12849 ⟨27,by decide⟩).lower ∧ (cell12849 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12849 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12849 ⟨28,by decide⟩).lower ∧ (cell12849 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12849 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12849 ⟨29,by decide⟩).lower ∧ (cell12849 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12849 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12849 ⟨30,by decide⟩).lower ∧ (cell12849 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12849 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12849 ⟨31,by decide⟩).lower ∧ (cell12849 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12849 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12849 ⟨32,by decide⟩).lower ∧ (cell12849 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12849 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12849 ⟨33,by decide⟩).lower ∧ (cell12849 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12849 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12849 ⟨34,by decide⟩).lower ∧ (cell12849 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12849 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12849 ⟨35,by decide⟩).lower ∧ (cell12849 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12849 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12849 ⟨36,by decide⟩).lower ∧ (cell12849 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12849 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12849 ⟨37,by decide⟩).lower ∧ (cell12849 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12849 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12849 ⟨38,by decide⟩).lower ∧ (cell12849 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12849 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12849 ⟨39,by decide⟩).lower ∧ (cell12849 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12849 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12849 ⟨40,by decide⟩).lower ∧ (cell12849 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12849 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12849 ⟨41,by decide⟩).lower ∧ (cell12849 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12849 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12849 ⟨42,by decide⟩).lower ∧ (cell12849 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12849 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12849 ⟨43,by decide⟩).lower ∧ (cell12849 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12849 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12849 ⟨44,by decide⟩).lower ∧ (cell12849 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12849 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12849 ⟨45,by decide⟩).lower ∧ (cell12849 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12849 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12849 ⟨46,by decide⟩).lower ∧ (cell12849 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12849 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12849 ⟨47,by decide⟩).lower ∧ (cell12849 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12849 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12849 ⟨48,by decide⟩).lower ∧ (cell12849 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12849 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12849 ⟨49,by decide⟩).lower ∧ (cell12849 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12849 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12849 ⟨50,by decide⟩).lower ∧ (cell12849 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12849 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12849 ⟨51,by decide⟩).lower ∧ (cell12849 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12849 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12849 ⟨52,by decide⟩).lower ∧ (cell12849 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12849 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12849 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12849 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12849,cell12849,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12849 i).lower ∧
    (cell12849 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12849 i).upper ≤ (0.532 : ℝ) ∧
    (cell12849 i).centre ≤ (0.1 : ℝ) ∧ (cell12849 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12849 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12849 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12849

/-! The local source numeric instances at 12849 have no network premises. -/
namespace BstLean.Part269.N12849
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12849)
open BstLean.Part268 (cell12849)

noncomputable def sourceNumerics12849 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12849 (cell12849 i)
      scalarRow12849.M scalarRow12849.H scalarRow12849.xi := by
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
    energy_allowance := scalarRow12849.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12849]
    centre_nonneg := (scalarRow12849.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D19.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12849])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12849